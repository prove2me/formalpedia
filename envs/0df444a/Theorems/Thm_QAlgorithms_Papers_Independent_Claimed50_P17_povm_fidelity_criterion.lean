-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P17_povm_fidelity_criterion
-- name    : QAlgorithms.Papers.Independent.Claimed50.P17.povm_fidelity_criterion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:52:12.962486+00:00
-- url     : https://prove2.me/theorems/f12078d8-7a7c-4403-9703-8714b637d574
-- title:
--   Fidelity criterion for rank-one basis measurements
-- statement:
--   Let $d>0$ and let $P=(P_i)_{i=1}^d$ and $Q=(Q_i)_{i=1}^d$ be POVMs on $\mathbb C^d$: all effects are positive semidefinite and each family sums to the identity. Suppose one family consists of the rank-one projectors onto an orthonormal basis. Define
--   $$F(P,Q)=\frac1d\sum_{i=1}^d\operatorname{Re}\operatorname{Tr}(P_iQ_i).$$
--   Then
--   $$F(P,Q)\le1,\qquad F(P,Q)=1\iff P_i=Q_i\ \text{for every }i.$$
--   This criterion distinguishes exact replication from approximation. Rank-one basis measurements, rather than arbitrary higher-rank projective measurements, are the objects used in the source proof.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, PDF p. 2, Lemma 1 (Fidelity criterion for POVM)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF p.2, Lemma 1. The proof's rank-one, full-basis
interpretation of von Neumann measurement is explicit; d is positive. -/
theorem povm_fidelity_criterion (d : ℕ) (hd : 0 < d)
    (P Q : Fin d → Op (Fin d)) (hP : IsPOVM P) (hQ : IsPOVM Q)
    (hBasis : IsRankOnePVM P ∨ IsRankOnePVM Q) :
    (povmFidelity P Q = 1 ↔ ∀ i, P i = Q i) ∧ povmFidelity P Q ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P17

end
