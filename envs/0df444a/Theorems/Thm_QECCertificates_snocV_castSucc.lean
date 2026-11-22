-- Prove2me | Theorems.Thm_QECCertificates_snocV_castSucc
-- name    : QECCertificates.snocV_castSucc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:42:22.194058+00:00
-- url     : https://prove2.me/theorems/b585f48c-92d3-476c-a58e-7dcc05b1d6ed
-- title:
--   QECCertificates: snoc V cast Succ
-- statement:
--   The QECCertificates construction uses the snoc V cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L74-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L74-L78

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.snocV_castSucc {u : Vec n} {b : ZMod 2} (i : Fin n) :
    snocV u b i.castSucc = u i := by sorry
