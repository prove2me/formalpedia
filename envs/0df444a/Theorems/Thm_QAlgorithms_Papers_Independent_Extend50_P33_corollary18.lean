-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_corollary18
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.corollary18
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:02:41.370331+00:00
-- url     : https://prove2.me/theorems/613767ba-9ce4-4969-a398-857d9d9483f0
-- title:
--   Corollary 18: common diagonal-block transposition trace (corrected subscript)
-- statement:
--   Let $R$ be an arbitrary unitary realization of the irreducible representation $\mu$ of $S_q$, where $q\ge1$. Let $\alpha\nearrow\mu$ denote all predecessor diagrams of size $q-1$, without a physical height restriction. Let $P_\alpha$ be the subgroup character projector and $C_\lambda$ the scalar of the sum of all transpositions in the irrep $\lambda$ (zero for an empty class). Assume $q\ge2$. For every $a<q$ and predecessor $\alpha$,
--
--   $$\operatorname{Tr}(P_\alpha R((a,q))P_\alpha)=\frac{d_\alpha}{q-1}(C_\mu-C_\alpha).$$
--
--   For degrees where both transposition characters exist this is $q d_\alpha\chi_\mu((12))/(2d_\mu)-(q-2)\chi_\alpha((12))/2$. The printed unbound $d_\beta$ is corrected to $d_\mu$, uniquely determined by tracing Eq.(51).
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 20, Corollary 18: common diagonal-block transposition trace (corrected subscript)

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

/-- PDF p.20 Corollary18, corrected d_beta to d_mu. The equivalent class-sum
form avoids a nonexistent transposition in S_1. r>0 permits division by r. -/
theorem corollary18 {r D : ℕ} (hr : 0 < r)
    (mu : Schur.Partition (r+1) (r+1))
    (R : Equiv.Perm (Fin (r+1)) →* Matrix.unitaryGroup (Fin D) ℂ)
    (hR : RealizesSpechtIrrep mu R) (a : Preds mu) (b : Fin r) :
    (subgroupProjector R a.val *
      (R (Equiv.swap b.castSucc (Fin.last r)) : Matrix (Fin D) (Fin D) ℂ) *
        subgroupProjector R a.val).trace =
      (((sdim a.val:ℝ) / r * (classScalar mu - classScalar a.val):ℝ):ℂ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
