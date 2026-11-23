-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:31.503169+00:00
-- url     : https://prove2.me/theorems/8ab0cb95-a33a-4496-9e7c-b5e9c3b87ce2
-- title:
--   P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing gt ev ev  a7884319006c: P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing gt ev ev  a7884319006c
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing gt ev ev  a7884319006c construction uses the P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing gt ev ev  a7884319006c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeTrans.lean#L303-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeTrans.lean#L303-L304

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c {l m n : ℕ} (V : Fin m → Pt k n d) (W : Fin l → Pt k m d) (hV : ∀ j, GP (V j))
    (hW : ∀ j, GP (W j)) (f : PS k l d) : ev V (ev W f) = ev (fun j => evP V (W j)) f := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«TB».«WickVanishing».«gt_ev_ev'» := P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
