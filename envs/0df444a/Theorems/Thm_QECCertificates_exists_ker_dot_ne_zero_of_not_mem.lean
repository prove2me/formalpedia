-- Prove2me | Theorems.Thm_QECCertificates_exists_ker_dot_ne_zero_of_not_mem
-- name    : QECCertificates.exists_ker_dot_ne_zero_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:00.965349+00:00
-- url     : https://prove2.me/theorems/b2e65052-127c-4259-8b3c-e9e52f7e2922
-- title:
--   QECCertificates: exists ker dot ne zero of not mem
-- statement:
--   **Separation lemma**: a vector outside the row space has nonzero dot product with some kernel
--   vector.
--
--   The construction is explicit: reduce `y` against the output of the elimination, so that the
--   residual `y'` is nonzero (otherwise `y` would lie in the row space) and vanishes on the pivot
--   columns; take the free column `j` at which `y'` is nonzero, and `kerVec D j` is the required kernel
--   vector (it is 1 on the free column `j` and 0 on the other free columns, while `y'` is nonzero only
--   on free columns).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L223-L283
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L223-L283

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.exists_ker_dot_ne_zero_of_not_mem {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    {y : Vec k} (h : y ∉ spanL (matRowList M)) :
    ∃ z : Vec k, M *ᵥ z = 0 ∧ y ⬝ᵥ z ≠ 0 := by sorry
