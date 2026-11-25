-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_le_molli_of_ge_599e6e036d92
-- name    : P2M_GroundTheory_Heights__Heights_Regular_le_molli_of_ge_599e6e036d92
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:56.151716+00:00
-- url     : https://prove2.me/theorems/1015e647-fa34-4767-b169-97efa5f644db
-- title:
--   P2 M Ground Theory Heights  Heights Regular le molli of ge 599e6e036d92: P2 M Ground Theory Heights  Heights Regular le molli of ge 599e6e036d92
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular le molli of ge 599e6e036d92 construction uses the P2 M Ground Theory Heights  Heights Regular le molli of ge 599e6e036d92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PChartMollifiedBounds.lean#L36-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PChartMollifiedBounds.lean#L36-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartMollifiedBounds
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
open Metric Filter Topology MeasureTheory Set
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt polyMax shrink)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_le_molli_of_ge_599e6e036d92 {D : ℕ} (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
    (hU : IsOpen U) (hφ : IsPsh U φ) {t c : ℝ} (ht : 0 < t) {z : Fin D → ℂ}
    (hz : closedBall z t ⊆ U) (hc : ∀ y ∈ closedBall z t, c ≤ φ y) : c ≤ molli ρ t φ z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«le_molli_of_ge» := P2M_GroundTheory_Heights__Heights_Regular_le_molli_of_ge_599e6e036d92
