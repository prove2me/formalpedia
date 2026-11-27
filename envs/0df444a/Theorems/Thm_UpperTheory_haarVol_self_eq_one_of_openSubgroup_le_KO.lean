-- Prove2me | Theorems.Thm_UpperTheory_haarVol_self_eq_one_of_openSubgroup_le_KO
-- name    : UpperTheory.haarVol_self_eq_one_of_openSubgroup_le_KO
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:50:34.568793+00:00
-- url     : https://prove2.me/theorems/36bb90c1-9b3f-4304-97cf-661336651da4
-- title:
--   Upper Theory: haar Vol self eq one of open Subgroup le KO
-- statement:
--   The Upper Theory construction uses the haar Vol self eq one of open Subgroup le KO property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DivisorFrames/HaarVolSelfEqOneOfOpenSubgroupLeKO.lean#L8-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DivisorFrames/HaarVolSelfEqOneOfOpenSubgroupLeKO.lean#L8-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ScaledIntegerPeriodic
import Definitions.Def_Development_AutomorphicArithmetic_DivisorFrames_HaarVolSelfEqOneOfOpenSubgroupLeKO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

theorem UpperTheory.haarVol_self_eq_one_of_openSubgroup_le_KO :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] (J : Subgroup (GL n k)), IsOpen (J : Set (GL n k)) → J ≤ KO k n → haarVol (J.map invT) (J : Set (GL n k)) = 1 := by sorry
