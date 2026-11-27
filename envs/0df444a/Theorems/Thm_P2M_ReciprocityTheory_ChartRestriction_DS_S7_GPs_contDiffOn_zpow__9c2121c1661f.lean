-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_GPs_contDiffOn_zpow__9c2121c1661f
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_S7_GPs_contDiffOn_zpow__9c2121c1661f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:44:13.767911+00:00
-- url     : https://prove2.me/theorems/479391ea-dfc1-4d57-9703-51c43a55d866
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS S7 GPs cont Diff On zpow  9c2121c1661f: P2 M Reciprocity Theory Chart Restriction DS S7 GPs cont Diff On zpow  9c2121c1661f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS S7 GPs cont Diff On zpow  9c2121c1661f construction uses the P2 M Reciprocity Theory Chart Restriction DS S7 GPs cont Diff On zpow  9c2121c1661f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsB.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsB.lean#L54-L59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs

theorem P2M_ReciprocityTheory_ChartRestriction_DS_S7_GPs_contDiffOn_zpow__9c2121c1661f {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {s : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hf : ContDiffOn ℂ ∞ f s) (h0 : ∀ x ∈ s, f x ≠ 0) (m : ℤ) : ContDiffOn ℂ ∞ (fun y => f y ^ m) s := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«S7».«GPs».«contDiffOn_zpow'» := P2M_ReciprocityTheory_ChartRestriction_DS_S7_GPs_contDiffOn_zpow__9c2121c1661f
