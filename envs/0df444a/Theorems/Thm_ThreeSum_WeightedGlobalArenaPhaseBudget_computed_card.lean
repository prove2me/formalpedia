-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_computed_card
-- name    : ThreeSum.WeightedGlobalArenaPhaseBudget.computed_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T01:04:57.628924+00:00
-- url     : https://prove2.me/theorems/26d20d8f-cc48-46de-9658-ffaa6d659712
-- title:
--   Weighted Global Arena Phase Budget: computed card
-- statement:
--   Cardinality of the exact found-field type in actual runtime dimensions.
--   This is the only scalar field identity consumed by prepared_good.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPhaseBudget.lean#L145-L151
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPhaseBudget.lean#L145-L151

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhase
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPhaseBudget
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSeedData WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters TernaryExtensionEncoding
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalArenaPhaseBudget.computed_card (M radix K n U c : ℕ)
    [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus p
      (LightWeightedGlobalDimensions.dim M radix p K n U) c))] :
    Fintype.card (AdjoinRoot (WeightedGlobalComputedExtensionMenu.modulus p
      (LightWeightedGlobalDimensions.dim M radix p K n U) c))=
      p^(menuDegree p (LightWeightedGlobalDimensions.J M radix n U+2) K) := by sorry
