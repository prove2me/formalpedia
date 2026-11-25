-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_luD__b54dad62ec55
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_luD__b54dad62ec55
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:13:49.205882+00:00
-- url     : https://prove2.me/theorems/ffd2a70e-5e58-4405-8ab1-11e01a05baab
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up MI det lu D  b54dad62ec55: P2 M Reciprocity Theory Chart Restriction G AR Up MI det lu D  b54dad62ec55
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up MI det lu D  b54dad62ec55 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up MI det lu D  b54dad62ec55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfA.lean#L209-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfA.lean#L209-L213

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_luD__b54dad62ec55 (w : Ix ι r → ℂ) :
    (luD' w).det = Complex.normSq (∏ i : Ix ι r, if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«MI».«det_luD'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_luD__b54dad62ec55
