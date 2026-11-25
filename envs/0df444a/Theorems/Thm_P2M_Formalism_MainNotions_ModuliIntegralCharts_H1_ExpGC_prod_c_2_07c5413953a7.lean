-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_prod_c_2_07c5413953a7
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_prod_c_2_07c5413953a7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:11.455824+00:00
-- url     : https://prove2.me/theorems/d82596cf-9682-4201-9d25-4608588f5b99
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GC prod c 2 07c5413953a7: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GC prod c 2 07c5413953a7
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GC prod c 2 07c5413953a7 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GC prod c 2 07c5413953a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CocycleProductThree.lean#L62-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CocycleProductThree.lean#L62-L83

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocycleProductThree
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
set_option maxHeartbeats 800000

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_prod_c_2_07c5413953a7 {T : Over Xo.X} {U : Type} [CommGroup U] (h : (T.left ⟶ Xo.univ.t.G.left) → U)
    (xs : Fin 2 → (T ⟶ Xo.univ.t.G)) :
    ∏ I : ULift (Finset (Fin 2)), h (cφ xs I) ^ cε 2 I =
      h (1 : T ⟶ Xo.univ.t.G).left * (h (xs 0 * 1).left)⁻¹ * (h (xs 1 * 1).left)⁻¹ * h (xs 0 * (xs 1 * 1)).left := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpGC».«prod_cφ2» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_prod_c_2_07c5413953a7
