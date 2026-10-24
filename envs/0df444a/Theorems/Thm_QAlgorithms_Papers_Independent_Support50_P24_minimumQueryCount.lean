-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P24_minimumQueryCount
-- name    : QAlgorithms.Papers.Independent.Support50.P24.minimumQueryCount
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:59:36.318058+00:00
-- url     : https://prove2.me/theorems/2d23dc82-6719-43fe-bba8-54ca6ceaef24
-- title:
--   Four calls are optimal without a supplied catalyst
-- statement:
--   Among deterministic causally ordered protocols using fixed CPTP stages and arbitrary finite memory, without a supplied $U$-dependent state, the minimum number of forward calls required for exact universal qubit-unitary inversion is four. A four-call circuit exists. Conversely,
--
--   $$\forall n\le3\;\forall A\;\exists U\in\mathrm{SU}(2)\;\exists\rho,\qquad
--   A[U](\rho)\ne U^\dagger\rho U,$$
--
--   where $A$ is any fixed $n$-call protocol and $\rho$ is a positive semidefinite trace-one qubit density matrix. The same unknown $U$ is used in all slots. The protocol, its memory and its CPTP maps are chosen before $U$ and $\rho$. This optimality statement concerns inversion without advice and does not assert optimality for catalytic or clean protocols.
-- source:
--   Reversing Unknown Qubit-Unitary Operation, Deterministically and Exactly, arXiv:2209.02907v5, PDF p. 4, Unnumbered corollary: four calls are optimal without a supplied catalyst

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P24

noncomputable section

open QAlgorithms MeasureTheory

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Support50.P24

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P24.groupedContinuousENorm

/-- PDF p.4: four calls are optimal among all finite-memory causally ordered CPTP
protocols without a supplied U-dependent state. The lower bound is cited to [21,27];
its separate proof dependency remains deferred, not inferred from rounded numerics. -/
theorem minimumQueryCount :
    (∃ gates : List CallGate, PhysicalCalls gates ∧ calls gates = 4 ∧ ExactInverter gates) ∧
    ∀ n : ℕ, n ≤ 3 → ∀ A : SequentialProtocol n,
      ∃ (U : QubitSU) (rho : Matrix Bool Bool ℂ), IsDensityMatrix rho ∧
        protocolOutput A U rho ≠ conjSuperop U.valᴴ rho := by sorry

end QAlgorithms.Papers.Independent.Support50.P24

end
