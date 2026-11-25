-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp_inv__19d087a4f878
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp_inv__19d087a4f878
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:14:28.747034+00:00
-- url     : https://prove2.me/theorems/cb0050fa-ff0e-4dd6-8ba7-b5294f74b6ae
-- title:
--   P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing gt comp inv  19d087a4f878: P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing gt comp inv  19d087a4f878
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing gt comp inv  19d087a4f878 construction uses the P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing gt comp inv  19d087a4f878 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeTrans.lean#L325-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeTrans.lean#L325-L328

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp_inv__19d087a4f878 {n : ℕ} {φ φi : Pt k 1 d} (h : IsInvPair φ φi) (a : Pt k n d) (ha : GP a) :
    comp1 φi (comp1 φ a) = a := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«TB».«WickVanishing».«gt_comp_inv'» := P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp_inv__19d087a4f878
