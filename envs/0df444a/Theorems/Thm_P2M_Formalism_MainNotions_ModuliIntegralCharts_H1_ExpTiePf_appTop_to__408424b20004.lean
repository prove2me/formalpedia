-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_appTop_to__408424b20004
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_appTop_to__408424b20004
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:21.955846+00:00
-- url     : https://prove2.me/theorems/8d1d57ba-9dfb-4ba2-ab9d-6c3d667e18c9
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Tie Pf app Top to  408424b20004: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Tie Pf app Top to  408424b20004
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Tie Pf app Top to  408424b20004 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Tie Pf app Top to  408424b20004 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTiePf.lean#L310-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTiePf.lean#L310-L314

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPowerSeries
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_appTop_to__408424b20004 {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) {A B : Type} [CommRing A] [Algebra S A] [CommRing B]
    [Algebra S B] (f : A →ₐ[S] B) (a : A) :
    ((Formalism.L2.Pj.homAt x0 f).left.appTop).hom (toΓ A a) = toΓ B (f a) := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpTiePf».«appTop_toΓ» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_appTop_to__408424b20004
