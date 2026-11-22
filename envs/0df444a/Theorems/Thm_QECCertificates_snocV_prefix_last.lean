-- Prove2me | Theorems.Thm_QECCertificates_snocV_prefix_last
-- name    : QECCertificates.snocV_prefix_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:43.930254+00:00
-- url     : https://prove2.me/theorems/9f09abda-e1a4-4abe-8be2-913b999ff4e1
-- title:
--   QECCertificates: snoc V prefix last
-- statement:
--   Every vector of `n+1` coordinates is reconstructed from its prefix and its last
--   coordinate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L95-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L95-L100

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.snocV_prefix_last (v : Vec (n + 1)) :
    snocV (fun i : Fin n => v i.castSucc) (v (Fin.last n)) = v := by sorry
