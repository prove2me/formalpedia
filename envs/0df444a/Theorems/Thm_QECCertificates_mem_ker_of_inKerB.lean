-- Prove2me | Theorems.Thm_QECCertificates_mem_ker_of_inKerB
-- name    : QECCertificates.mem_ker_of_inKerB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:49.843797+00:00
-- url     : https://prove2.me/theorems/63643ed5-1c9e-4d1b-b03c-90077393b6f5
-- title:
--   QECCertificates: mem ker of in Ker B
-- statement:
--   Kernel membership from a computable decision.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L255-L257
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L255-L257

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

theorem QECCertificates.mem_ker_of_inKerB {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) {v : Vec n}
    (h : inKerB M v = true) : v ∈ LinearMap.ker M.toLin' := by sorry
