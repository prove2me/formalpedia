-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_tResourceConjugateWord_mem_generated
-- name    : QEC.Distillation.OneQubitMagic.tResourceConjugateWord_mem_generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:07:08.175094+00:00
-- url     : https://prove2.me/theorems/29d290f2-00b5-40a7-ac08-ee0995e446d9
-- title:
--   One Qubit Magic: t Resource Conjugate Word mem generated
-- statement:
--   The conjugate word remains in the generated Clifford-plus-phase subgroup.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TPhaseGeneratedUniversality.lean#L200-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TPhaseGeneratedUniversality.lean#L200-L205

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.tResourceConjugateWord_mem_generated :
    tResourceConjugateWord ∈
      generatedUnitarySubgroup (cliffordPhaseGenerators tResourcePhaseAngle) := by sorry
