-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_hAngleConjugateWord_mem_generated
-- name    : QEC.Distillation.OneQubitMagic.hAngleConjugateWord_mem_generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:06:03.629488+00:00
-- url     : https://prove2.me/theorems/8320ddb7-5cbe-445e-9007-d72f19fcca2c
-- title:
--   One Qubit Magic: h Angle Conjugate Word mem generated
-- statement:
--   The One Qubit Magic construction uses the h Angle Conjugate Word mem generated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/HAngleUniversality.lean#L234-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/HAngleUniversality.lean#L234-L238

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.hAngleConjugateWord_mem_generated :
    hAngleConjugateWord ∈ generatedUnitarySubgroup
      (cliffordPhaseGenerators (-Real.pi / 4)) := by sorry
