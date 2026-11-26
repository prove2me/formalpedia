-- Prove2me | Theorems.Thm_StrongContUnitary_generator_isSelfAdjoint
-- name    : StrongContUnitary.generator_isSelfAdjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:34.731616+00:00
-- url     : https://prove2.me/theorems/e49fc979-ff7b-5c3f-bddf-3792b1f07bc0
-- title:
--   Strong Cont Unitary: generator is Self Adjoint
-- statement:
--   The Strong Cont Unitary construction uses the generator is Self Adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Stone/SelfAdjoint.lean#L599-L604
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Stone/SelfAdjoint.lean#L599-L604

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Definitions.Def_Spectral_Stone_Generator
import Definitions.Def_Spectral_Stone_SelfAdjoint
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
open StrongContUnitary
open MeasureTheory Filter

theorem StrongContUnitary.generator_isSelfAdjoint
    (U : StrongContUnitary E) :
    IsSelfAdjoint U.generator := by sorry
