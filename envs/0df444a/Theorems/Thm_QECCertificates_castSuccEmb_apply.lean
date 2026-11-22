-- Prove2me | Theorems.Thm_QECCertificates_castSuccEmb_apply
-- name    : QECCertificates.castSuccEmb_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:42:24.900225+00:00
-- url     : https://prove2.me/theorems/f36cd2f3-5bb9-493b-ad78-8bf989f51557
-- title:
--   QECCertificates: cast Succ Emb apply
-- statement:
--   The QECCertificates construction uses the cast Succ Emb apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L80-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L80-L80

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.castSuccEmb_apply (i : Fin n) : Fin.castSuccEmb i = i.castSucc := by sorry

attribute [defeq] QECCertificates.castSuccEmb_apply
