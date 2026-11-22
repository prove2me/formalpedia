-- Prove2me | Theorems.Thm_QECCertificates_LRAT_unsat_of_checkSteps
-- name    : QECCertificates.LRAT.unsat_of_checkSteps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:36.717892+00:00
-- url     : https://prove2.me/theorems/6339059a-eff7-4930-a5ba-fb24922b2801
-- title:
--   LRAT: unsat of check Steps
-- statement:
--   The entry point used by the generator: the same content as `checkSteps_sound`, as a
--   proof term.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/LRAT.lean#L406-L407
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/LRAT.lean#L406-L407

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

theorem QECCertificates.LRAT.unsat_of_checkSteps {F : CNF} {steps : List LStep}
    (h : checkSteps F steps = true) : ¬ Satisfiable F := by sorry
