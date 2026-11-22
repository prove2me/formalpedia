-- Prove2me | Theorems.Thm_QECCertificates_eq_minWeight_of_decide
-- name    : QECCertificates.eq_minWeight_of_decide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:24.172393+00:00
-- url     : https://prove2.me/theorems/5200a75a-1bf5-41b2-8379-6fcdfc5b0996
-- title:
--   QECCertificates: eq min Weight of decide
-- statement:
--   **The exact distance, checkable certificate form**: the lower bound by `decide` and an
--   explicit witness for the upper bound pinch to an equality.
--
--   This is a uniform proof template for concrete parity-check matrices. For a code, only
--   four things have to be supplied: (i) two parity-check matrices, (ii) an explicit low-weight
--   logical operator `E`, (iii) three closed assertions the kernel can compute, namely that
--   `E` is in the kernel, that `E` is not in the row space, and that `hammingNorm E = d`, and
--   (iv) an empty `lightSet`. **No step refers to an external solver or to a custom axiom.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L219-L226
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L219-L226

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Definitions.Def_LeanPool_QECCertificates_GF2_LowerBound
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.eq_minWeight_of_decide {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : d ≤ n) (hlow : (lightSet M₁ M₂ d).card = 0) {E : Vec n}
    (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.certificateRowSpace) (hw : hammingNorm E =
      d) :
    minWeightKernelOutsideRowSpace M₁ M₂ = d := by sorry
