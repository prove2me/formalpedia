-- Prove2me | Theorems.Thm_QECCertificates_LRAT_checkSteps_sound
-- name    : QECCertificates.LRAT.checkSteps_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:52.272729+00:00
-- url     : https://prove2.me/theorems/1abe2043-5139-4223-8837-952e5121d914
-- title:
--   LRAT: check Steps sound
-- statement:
--   **The main theorem, entry point**: a successful kernel check implies that the CNF is
--   unsatisfiable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/LRAT.lean#L398-L402
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/LRAT.lean#L398-L402

module
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Std.Data.TreeMap.Lemmas
public import Std.Data.DTreeMap.Lemmas
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.checkSteps_sound {F : CNF} {steps : List LStep}
    (h : checkSteps F steps = true) : ¬ Satisfiable F := by sorry
