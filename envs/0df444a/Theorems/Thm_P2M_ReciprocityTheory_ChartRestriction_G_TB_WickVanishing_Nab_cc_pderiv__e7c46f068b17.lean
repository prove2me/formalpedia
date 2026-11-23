-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_pderiv__e7c46f068b17
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_pderiv__e7c46f068b17
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:51.286509+00:00
-- url     : https://prove2.me/theorems/4c3ab66e-d754-4763-8d38-ae4de2961b5b
-- title:
--   P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing Nab cc pderiv  e7c46f068b17: P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing Nab cc pderiv  e7c46f068b17
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing Nab cc pderiv  e7c46f068b17 construction uses the P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing Nab cc pderiv  e7c46f068b17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ConstantCoeffAddFirstSecond.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ConstantCoeffAddFirstSecond.lean#L15-L18

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyPointZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffAddFirstSecond
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
variable {k : Type} [CommRing k] {d : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_pderiv__e7c46f068b17 {n : ℕ} (f : PS k n d) (v : Fin n × Fin d) :
    constantCoeff (pderiv k v f) = coeff (Finsupp.single v 1) f := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«TB».«WickVanishing».«Nab».«cc_pderiv'» := P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_pderiv__e7c46f068b17
