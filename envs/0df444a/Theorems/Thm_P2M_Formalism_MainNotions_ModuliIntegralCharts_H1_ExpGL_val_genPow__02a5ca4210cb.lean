-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGL_val_genPow__02a5ca4210cb
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGL_val_genPow__02a5ca4210cb
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:01:55.717826+00:00
-- url     : https://prove2.me/theorems/495d0888-1ba7-409f-b00c-7e647da6b746
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GL val gen Pow  02a5ca4210cb: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GL val gen Pow  02a5ca4210cb
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GL val gen Pow  02a5ca4210cb construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GL val gen Pow  02a5ca4210cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CocChart.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CocChart.lean#L21-L28

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpSActPS
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BqOriginSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocChart
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGL
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
  Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGK
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGL_val_genPow__02a5ca4210cb {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (k : ℕ) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) : val (genPow φ ε g k) r z J = val g r z J ^ k := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpGL».«val_genPow'» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGL_val_genPow__02a5ca4210cb
