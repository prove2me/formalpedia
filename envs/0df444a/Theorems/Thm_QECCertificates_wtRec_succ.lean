-- Prove2me | Theorems.Thm_QECCertificates_wtRec_succ
-- name    : QECCertificates.wtRec_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:43:45.37722+00:00
-- url     : https://prove2.me/theorems/5b8662ce-23fa-4b98-95f3-ba2f2171c250
-- title:
--   QECCertificates: wt Rec succ
-- statement:
--   The QECCertificates construction uses the wt Rec succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L115-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L115-L118

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.wtRec_succ (v : Vec (n + 1)) :
    wtRec (n + 1) v
      = wtRec n (fun i => v i.castSucc) + (if v (Fin.last n) = 0 then 0 else 1) := by sorry
