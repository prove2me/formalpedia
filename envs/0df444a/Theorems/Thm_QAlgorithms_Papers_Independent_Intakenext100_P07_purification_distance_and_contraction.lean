-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_purification_distance_and_contraction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.purification_distance_and_contraction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:58:55.324196+00:00
-- url     : https://prove2.me/theorems/e180a0e5-6dff-4702-8bf7-057cf8831192
-- title:
--   §3.4 (3.48)–(3.49): purification interpretation and contraction
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$.
--
--   For normalized states P(ρ,τ) is the minimum trace distance between their purifications on a sufficiently large common auxiliary system; for subnormalized inputs P contracts under CPTNI maps.
--
--   $$
--   P(\rho,\tau)=\min_{\varphi,\vartheta\text{ purifications}}\Delta(\varphi,\vartheta),\qquad P(\mathcal F(\rho),\mathcal F(\tau))\le P(\rho,\tau).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 47, §3.4 (3.48)–(3.49): purification interpretation and contraction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#3.purificationmetric
§3.4 (3.48)–(3.49): purification interpretation and contraction, arXiv:1504.00233v5, PDF p.47. -/
theorem purification_distance_and_contraction [Nonempty I] [Nonempty J] :
    (∀ r s : paperMat I, IsDensityMatrix r → IsDensityMatrix s → Fintype.card I ≤ Fintype.card J →
      (∃ R S : paperMat (I × J), IsDensityMatrix R ∧ IsDensityMatrix S ∧ paperPure R ∧ paperPure S ∧
        traceRight R = r ∧ traceRight S = s ∧ paperDelta R S = purified r s) ∧
      (∀ R S : paperMat (I × J), IsDensityMatrix R → IsDensityMatrix S → paperPure R → paperPure S →
        traceRight R = r → traceRight S = s → purified r s ≤ paperDelta R S)) ∧
    (∀ E : paperMat I →ₗ[ℂ] paperMat J, CPTNI E → ∀ r s : paperMat I, paperSubnormalized r → paperSubnormalized s →
      purified (E r) (E s) ≤ purified r s) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
