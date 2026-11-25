-- Prove2me | Theorems.Thm_PI_GGConvScalarW_representation_conjugation_apply
-- name    : PI.GGConvScalarW.representation_conjugation_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:30:53.276594+00:00
-- url     : https://prove2.me/theorems/c0df6884-56bb-5358-90db-892e2c075537
-- title:
--   GGConv Scalar W: representation conjugation apply
-- statement:
--   The GGConv Scalar W construction uses the representation conjugation apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/Reindex.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/Reindex.lean#L39-L44

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic Finset

theorem PI.GGConvScalarW.representation_conjugation_apply {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin k) F) V) (y x : GL (Fin k) F) (v : V) :
    π y⁻¹ (π (y * x * y⁻¹) (π y v)) = π x v := by sorry
