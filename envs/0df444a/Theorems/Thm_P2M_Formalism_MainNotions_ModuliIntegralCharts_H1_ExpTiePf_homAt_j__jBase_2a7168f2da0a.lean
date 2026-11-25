-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_homAt_j__jBase_2a7168f2da0a
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_homAt_j__jBase_2a7168f2da0a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:01:33.902408+00:00
-- url     : https://prove2.me/theorems/a184d7b4-18a5-4369-81d4-aa02157810b9
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Tie Pf hom At j  j Base 2a7168f2da0a: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Tie Pf hom At j  j Base 2a7168f2da0a
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Tie Pf hom At j  j Base 2a7168f2da0a construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Tie Pf hom At j  j Base 2a7168f2da0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTiePf.lean#L304-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTiePf.lean#L304-L308

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

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_homAt_j__jBase_2a7168f2da0a {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)]
    (y : FrPt Xo c S) (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    Formalism.L2.Pj.homAt y.x (jφ φ m) ≫ jBase y C.d m 1 = jBase y (dL Dw) m 1 := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpTiePf».«homAt_jφ_jBase» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_homAt_j__jBase_2a7168f2da0a
