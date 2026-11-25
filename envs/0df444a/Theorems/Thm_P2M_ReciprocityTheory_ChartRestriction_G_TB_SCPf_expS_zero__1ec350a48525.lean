-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_SCPf_expS_zero__1ec350a48525
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_TB_SCPf_expS_zero__1ec350a48525
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:17:43.503944+00:00
-- url     : https://prove2.me/theorems/b6703897-cf0d-5b89-aa02-880d38848935
-- title:
--   P2 M Reciprocity Theory Chart Restriction G TB SCPf exp S zero  1ec350a48525: P2 M Reciprocity Theory Chart Restriction G TB SCPf exp S zero  1ec350a48525
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G TB SCPf exp S zero  1ec350a48525 construction uses the P2 M Reciprocity Theory Chart Restriction G TB SCPf exp S zero  1ec350a48525 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LiftXEqRename.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LiftXEqRename.lean#L16-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_DivPowInteg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXEqRename
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem P2M_ReciprocityTheory_ChartRestriction_G_TB_SCPf_expS_zero__1ec350a48525 {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«TB».«SCPf».«expS_zero'» := P2M_ReciprocityTheory_ChartRestriction_G_TB_SCPf_expS_zero__1ec350a48525
