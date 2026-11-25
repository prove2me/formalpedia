-- Prove2me | Theorems.Thm_PI_GGConvScalarW_whit_sgn_projQ
-- name    : PI.GGConvScalarW.whit_sgn_projQ
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:31:25.80037+00:00
-- url     : https://prove2.me/theorems/a7593f7f-0612-46a4-89d6-87838d53b3b5
-- title:
--   GGConv Scalar W: whit sgn proj Q
-- statement:
--   The GGConv Scalar W construction uses the whit sgn proj Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/IntertwinerRankLeOne.lean#L26-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/IntertwinerRankLeOne.lean#L26-L40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_AveragingOperatorIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_IntertwinerRankLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem PI.GGConvScalarW.whit_sgn_projQ (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) (ℓ : Module.Dual ℂ V)
    (hℓ : IsWhit ψ₀ π ℓ) (v : V) : ℓ (π (sgn k) (projQ ψ₀ π v)) = ℓ (π (sgn k) v) := by sorry
