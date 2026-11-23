-- Prove2me | Theorems.Thm_P2M_GlobalTheory_QuadDeriv_constantCoeff_up_eq_zero__83ee02ec8fbc
-- name    : P2M_GlobalTheory_QuadDeriv_constantCoeff_up_eq_zero__83ee02ec8fbc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:07.816442+00:00
-- url     : https://prove2.me/theorems/c9de186b-bb77-47bf-ba0f-b44cf5f4a2cd
-- title:
--   P2 M Global Theory Quad Deriv constant Coeff up eq zero  83ee02ec8fbc: P2 M Global Theory Quad Deriv constant Coeff up eq zero  83ee02ec8fbc
-- statement:
--   The P2 M Global Theory Quad Deriv constant Coeff up eq zero  83ee02ec8fbc construction uses the P2 M Global Theory Quad Deriv constant Coeff up eq zero  83ee02ec8fbc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSecondPointDerivativeSecondCoordinate.lean#L195-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSecondPointDerivativeSecondCoordinate.lean#L195-L195

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.QuadDeriv
variable {k : Type} [CommRing k] {d : ℕ}

theorem P2M_GlobalTheory_QuadDeriv_constantCoeff_up_eq_zero__83ee02ec8fbc {a : Pt k 2 d} (ha : GP a) : GP (up a) := by sorry

alias «GlobalTheory».«QuadDeriv».«constantCoeff_up_eq_zero₂» := P2M_GlobalTheory_QuadDeriv_constantCoeff_up_eq_zero__83ee02ec8fbc
