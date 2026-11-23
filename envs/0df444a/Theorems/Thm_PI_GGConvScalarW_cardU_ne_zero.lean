-- Prove2me | Theorems.Thm_PI_GGConvScalarW_cardU_ne_zero
-- name    : PI.GGConvScalarW.cardU_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:41.904613+00:00
-- url     : https://prove2.me/theorems/10c89a4e-a323-44bf-a25d-ed5dfe311903
-- title:
--   GGConv Scalar W: card U ne zero
-- statement:
--   The GGConv Scalar W construction uses the card U ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/CardUNeZero.lean#L69-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/CardUNeZero.lean#L69-L78

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
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

theorem PI.GGConvScalarW.cardU_ne_zero (F : Type) [Field F] [Fintype F] (k : ℕ) : (cardU F k : ℂ) ≠ 0 := by sorry
