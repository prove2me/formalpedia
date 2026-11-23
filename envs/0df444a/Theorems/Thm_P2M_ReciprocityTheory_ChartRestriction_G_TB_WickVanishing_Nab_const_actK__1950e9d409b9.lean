-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_const_actK__1950e9d409b9
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_const_actK__1950e9d409b9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:34.165651+00:00
-- url     : https://prove2.me/theorems/f09336b9-f951-47f2-9a1b-fb107199e913
-- title:
--   P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing Nab const act K  1950e9d409b9: P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing Nab const act K  1950e9d409b9
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing Nab const act K  1950e9d409b9 construction uses the P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing Nab const act K  1950e9d409b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/FirstDerivativeShiftIntegral.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/FirstDerivativeShiftIntegral.lean#L14-L16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FirstDerivativeShiftIntegral
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_const_actK__1950e9d409b9 (B : FB R d O) (a : O) (l : Fin d) : constantCoeff (B.actK k a l) = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«TB».«WickVanishing».«Nab».«const_actK'» := P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_const_actK__1950e9d409b9
