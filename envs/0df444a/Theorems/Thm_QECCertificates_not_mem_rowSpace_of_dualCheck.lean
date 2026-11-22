-- Prove2me | Theorems.Thm_QECCertificates_not_mem_rowSpace_of_dualCheck
-- name    : QECCertificates.not_mem_rowSpace_of_dualCheck
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:45.443736+00:00
-- url     : https://prove2.me/theorems/60f83ff5-1fd0-4161-b8db-b61b1e1c0071
-- title:
--   QECCertificates: not mem row Space of dual Check
-- statement:
--   **The dual witness route**: `w ∈ ker H` together with `w ⬝ᵥ E = 1` implies
--   `E ∉ certificateRowSpace H`.
--
--   Both assertions are row-by-row pairings, so row reduction is not needed. This route
--   can avoid expensive reduction on wide matrices when a dual witness is available.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L264-L266
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L264-L266

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

theorem QECCertificates.not_mem_rowSpace_of_dualCheck {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    {E w : Vec n} (hk : inKerB H w = true) (hp : w ⬝ᵥ E = 1) : E ∉ H.certificateRowSpace := by sorry
