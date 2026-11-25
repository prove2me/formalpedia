-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_exists_lipschitz_near_compact_eeaef94d801a
-- name    : P2M_GroundTheory_Heights__Heights_Regular_exists_lipschitz_near_compact_eeaef94d801a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:30:55.711566+00:00
-- url     : https://prove2.me/theorems/82de9d63-7a36-57bc-bb81-f527b92e29e0
-- title:
--   P2 M Ground Theory Heights  Heights Regular exists lipschitz near compact eeaef94d801a: P2 M Ground Theory Heights  Heights Regular exists lipschitz near compact eeaef94d801a
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular exists lipschitz near compact eeaef94d801a construction uses the P2 M Ground Theory Heights  Heights Regular exists lipschitz near compact eeaef94d801a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedChartComparison.lean#L17-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedChartComparison.lean#L17-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsCompactImageClosureMid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartComparison
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PBoundedChartComparison
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_mono__555a93f5b347
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_polyMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_mollify_thm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Set
open ReciprocityTheory.AnForm.A (IsPsh polyMax molli mollify_thm polyMax_le' polyMax_mono' le_polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_exists_lipschitz_near_compact_eeaef94d801a {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {K W : Set E}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) (hf : ∀ y ∈ W, ContDiffAt ℝ 1 f y) :
    ∃ δ > 0, ∃ L : ℝ, ∀ z ∈ K, ∀ y ∈ closedBall z δ, y ∈ W ∧ ‖f y - f z‖ ≤ L * ‖y - z‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«exists_lipschitz_near_compact» := P2M_GroundTheory_Heights__Heights_Regular_exists_lipschitz_near_compact_eeaef94d801a
