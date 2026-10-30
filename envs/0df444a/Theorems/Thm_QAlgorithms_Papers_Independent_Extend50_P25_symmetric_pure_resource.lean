-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_symmetric_pure_resource
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.symmetric_pure_resource
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:21:33.460168+00:00
-- url     : https://prove2.me/theorems/fceb4380-74b8-40e5-b042-57b53f39985d
-- title:
--   Proposition 3.3: symmetric pure resource suffices
-- statement:
--   For every deterministic PBT protocol with $d,N\ge1$, there is a replacement with Alice and Bob each holding $N$ $d$-dimensional systems and a unit pure resource $|\psi\rangle$, satisfying
--   $$ (P_\pi\otimes P_\pi)|\psi\rangle=|\psi\rangle,\qquad(\overline U^{\otimes N}\otimes U^{\otimes N})|\psi\rangle=|\psi\rangle.$$
--   Its Bob marginal is invariant under permutations and diagonal $U(d)$. Its fidelity is no smaller, its full diamond error no larger, and no convex invariant channel cost increases. This selects a symmetric purification rather than restricting Bob to the totally symmetric subspace.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 15, Proposition 3.3: symmetric pure resource suffices

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Proposition 3.3, PDF p.15: a pure symmetric purification of a symmetric Werner
marginal suffices, with no-worse fidelity, diamond error and convex invariant costs. -/
theorem symmetric_pure_resource {d N : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N)
    {A : Type*} [Fintype A] [DecidableEq A] (P : PBTProtocol d N A) :
    ∃ Q : PBTProtocol d N (Ports d N),
      SymmetricPurification Q.resource ∧ NoWorse Q.channel P.channel := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
