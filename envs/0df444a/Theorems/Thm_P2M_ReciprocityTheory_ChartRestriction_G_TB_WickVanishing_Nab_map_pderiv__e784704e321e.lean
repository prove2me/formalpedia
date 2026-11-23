-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_map_pderiv__e784704e321e
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_map_pderiv__e784704e321e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:47.462364+00:00
-- url     : https://prove2.me/theorems/b78f00f3-a161-43b4-9006-e8b9bcd07322
-- title:
--   P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing Nab map pderiv  e784704e321e: P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing Nab map pderiv  e784704e321e
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing Nab map pderiv  e784704e321e construction uses the P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing Nab map pderiv  e784704e321e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/IntegralFamilyPointZero.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/IntegralFamilyPointZero.lean#L27-L35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyPointZero
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
variable (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k]
variable {R k}

theorem P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_map_pderiv__e784704e321e {σ : Type} (f : MvPowerSeries σ R) (v : σ) :
    MvPowerSeries.map (algebraMap R k) (pderiv R v f) = pderiv k v (MvPowerSeries.map (algebraMap R k) f) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«TB».«WickVanishing».«Nab».«map_pderiv'» := P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_map_pderiv__e784704e321e
