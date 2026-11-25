-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lowPt_ok
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.lowPt_ok
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:45:56.96795+00:00
-- url     : https://prove2.me/theorems/c677ff71-af0d-5b70-bc4d-141b3dcf9c02
-- title:
--   Lap: low Pt ok
-- statement:
--   The Lap construction uses the low Pt ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/InterlacesULt.lean#L213-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/InterlacesULt.lean#L213-L286

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_InterlacesULt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS

theorem ReciprocityTheory.ChartRestriction.DS.Lap.lowPt_ok {k r : ℕ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} {h : ℝ}
    (hk : 1 ≤ k) (hHC : IsHCPar (parLam k r v b)) (hI : Interlaces k r u v b)
    (hH : HalfInts k r u v b) (hG : LowGaps r b h) (i : ℕ) (hi : i < k) (hin : i < 2 * r + k + 1)
    (x : ℝ) (m : ℤ) (hx : x = parLam k r v b ⟨i, hin⟩ + m) (hlo : parLam k r v b ⟨i, hin⟩ ≤ x)
    (hhi : x ≤ u ⟨i, hi⟩ - 1 / 2) :
    IsHCPar (lowPt k r u v b i x) ∧ GapAtLeast (parEps k r) (lowPt k r u v b i x) h := by sorry
