-- Prove2me | Theorems.Thm_QECCertificates_lightVecs_succ_succ
-- name    : QECCertificates.lightVecs_succ_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:47:00.395067+00:00
-- url     : https://prove2.me/theorems/56ad2fd3-2130-4a26-ac95-5c7f751efaf8
-- title:
--   QECCertificates: light Vecs succ succ
-- statement:
--   The QECCertificates construction uses the light Vecs succ succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L140-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L140-L143

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.lightVecs_succ_succ (n w : ℕ) :
    lightVecs (n + 1) (w + 1) = (lightVecs n (w + 1)).map (fun u => snocV u 0)
      ++ (lightVecs n w).map (fun u => snocV u 1) := by sorry
