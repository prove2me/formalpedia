-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_thetaC_surjective
-- name    : Reformulated.AutPerF.BdRPlus.thetaC_surjective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:48:57.718301+00:00
-- url     : https://prove2.me/theorems/5c93fd5c-8c96-59da-ac90-768792f37e54
-- title:
--   Bd RPlus: theta C surjective
-- statement:
--   The Bd RPlus construction uses the theta C surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Embedding.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Embedding.lean#L37-L41

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_UniformContinuousConstSMulOfIsIsometricSMul
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Embedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {C : Type u} [NormedField C] [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)]
variable (O : ValuationSubring C) [IsUnitBall O]
open Reformulated.AutPerF.BdRPlus
variable {p O}

theorem Reformulated.AutPerF.BdRPlus.thetaC_surjective [IsAlgClosed C] : Function.Surjective (thetaC p O) := by sorry
