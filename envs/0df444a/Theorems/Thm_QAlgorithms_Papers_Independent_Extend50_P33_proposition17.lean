-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_proposition17
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.proposition17
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:01:43.532117+00:00
-- url     : https://prove2.me/theorems/1bbafd54-a9c6-4f6f-b236-dd35a887c0d0
-- title:
--   Proposition 17: bilinear PRIR sum rule
-- statement:
--   Let $R$ be an arbitrary unitary realization of the irreducible representation $\mu$ of $S_q$, where $q\ge1$. Let $\alpha\nearrow\mu$ denote all predecessor diagrams of size $q-1$, without a physical height restriction. Let $P_\alpha$ be the subgroup character projector and $C_\lambda$ the scalar of the sum of all transpositions in the irrep $\lambda$ (zero for an empty class). For every predecessor $\beta$, include the identity representative $(q,q)=1$. Then
--
--   $$\sum_{a=1}^{q}R((a,q))P_\beta R((a,q))=q\frac{d_\beta}{d_\mu}I.$$
--
--   Taking the $(\alpha,\gamma)$ block and its matrix entries in any partially reduced orthonormal basis yields exactly $\sum_{a,k_\beta}R^{\alpha\beta}_{i_\alpha k_\beta}((a,q))R^{\beta\gamma}_{k_\beta j_\gamma}((a,q))=q(d_\beta/d_\mu)\delta_{\alpha\gamma}\delta_{i_\alpha j_\gamma}$. Swaps are self-inverse, so no extra conjugation is inserted.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 19, Proposition 17: bilinear PRIR sum rule

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P33

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted type constructors; local notation only reorders Word's arguments.

local notation "Word" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P58.Word r d)

local notation "Op" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P21.Op
    (QAlgorithms.Papers.Independent.Information100.P58.Word r d))

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

/-- PDF pp.19–20 Proposition17: the bilinear block identity written as the
full-matrix identity whose alpha,gamma compression gives Eq.(56).
The sum includes the identity representative b=r. -/
theorem proposition17 {r D : ℕ} (mu : Schur.Partition (r+1) (r+1))
    (R : Equiv.Perm (Fin (r+1)) →* Matrix.unitaryGroup (Fin D) ℂ)
    (hR : RealizesSpechtIrrep mu R) (a : Preds mu) :
    ∑ b : Fin (r+1),
      (R (Equiv.swap b (Fin.last r)) : Matrix (Fin D) (Fin D) ℂ) *
        subgroupProjector R a.val *
      (R (Equiv.swap b (Fin.last r)) : Matrix (Fin D) (Fin D) ℂ) =
        (((r+1:ℕ):ℂ) * (sdim a.val:ℂ) / (sdim mu:ℂ)) • 1 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
