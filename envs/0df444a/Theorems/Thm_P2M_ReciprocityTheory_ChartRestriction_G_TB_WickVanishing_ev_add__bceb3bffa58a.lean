-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_add__bceb3bffa58a
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_add__bceb3bffa58a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:35.684795+00:00
-- url     : https://prove2.me/theorems/4c6ca9d7-f62d-4300-b2a2-b0edc3583985
-- title:
--   P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing ev add  bceb3bffa58a: P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing ev add  bceb3bffa58a
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing ev add  bceb3bffa58a construction uses the P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing ev add  bceb3bffa58a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcAdd.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcAdd.lean#L67-L70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]

theorem P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_add__bceb3bffa58a {n m d : ℕ} (b : Fin m → Pt k n d) (hb : ∀ j i, constantCoeff (b j i) = 0) (f g : PS k m d) :
    ev b (f + g) = ev b f + ev b g := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«TB».«WickVanishing».«ev_add'» := P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_add__bceb3bffa58a
