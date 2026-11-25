-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_haar_units
-- name    : PositivityTheory.ThKG.Loc.Bump.haar_units
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:04:45.099995+00:00
-- url     : https://prove2.me/theorems/2b4690a4-45cb-4ee5-806e-3b8101220710
-- title:
--   Bump: haar units
-- statement:
--   The Bump construction uses the haar units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/DictHaar.lean#L60-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/DictHaar.lean#L60-L111

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_DictHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
variable {ι : Type} [Fintype ι]

theorem PositivityTheory.ThKG.Loc.Bump.haar_units {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (j : G → ι → ℂ) (hj : IsOpenEmbedding j) (hr : range j = {c | ∀ w, c w ≠ 0}) (hm : ∀ a b, j (a * b) = j a * j b)
    (x : Measure G) [x.IsHaarMeasure] : ∃ κ : ℝ, 0 < κ ∧ ∀ g : (ι → ℂ) → ℂ,
      ∫ l, g (j l) ∂x = κ * ∫ c, g c * ((∏ w, ‖c w‖ ^ 2 : ℝ) : ℂ)⁻¹ := by sorry
