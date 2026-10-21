-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_tripartite_flower_values
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.tripartite_flower_values
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:44:27.608239+00:00
-- url     : https://prove2.me/theorems/b7af3270-3090-46ac-9238-4d8da702bdd4
-- title:
--   Proposition 6: tripartite flower values and one-qubit erasure
-- statement:
--   Let $d\ge1$ and let $\phi_d$ be the tripartite flower state obtained by tracing $X$ from
--
--   $$|\Phi_d\rangle=\frac1{\sqrt{2d}}\sum_{i=0}^{d-1}\sum_{j=0}^1|i,j\rangle_{AA'}|i,j\rangle_{BB'}|i,j\rangle_{CC'}U_j|i\rangle_X,$$
--
--   with $U_0=1$ and $U_1$ the normalized unitary discrete Fourier transform. In bits and without the squashing factor $1/2$,
--
--   $$E_{I_3}^q(\phi_d)=3+\log_2d,\qquad E_{I_3}^c(\phi_d)=3+\tfrac32\log_2d,$$
--   $$E_{S_3}^q(\phi_d)=E_{S_3}^c(\phi_d)=3+\log_2d.$$
--
--   After losing $A'$ all four values are zero. The formal erased state includes replacement of the lost flag by a fixed local pure zero flag, which preserves these values. This explicitly computes the locking example.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 7, Proposition 6: tripartite flower values and one-qubit erasure

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 6, PDF pp.7–8: all four tripartite values and erasure of
one local flag. The reset zero flag is a local pure ancilla. -/
theorem tripartite_flower_values (d : ℕ) (hd : 0 < d) :
    multipartiteSquashed false .total (multipartiteFlower 3 d) = 3 + Real.logb 2 d ∧
    multipartiteSquashed true .total (multipartiteFlower 3 d) = 3 + (3/2 : ℝ) * Real.logb 2 d ∧
    multipartiteSquashed false .dual (multipartiteFlower 3 d) = 3 + Real.logb 2 d ∧
    multipartiteSquashed true .dual (multipartiteFlower 3 d) = 3 + Real.logb 2 d ∧
    ∀ (classical : Bool) (kind : InformationKind),
      multipartiteSquashed classical kind (eraseFlowerFlag (0 : Fin 3) (multipartiteFlower 3 d)) = 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
