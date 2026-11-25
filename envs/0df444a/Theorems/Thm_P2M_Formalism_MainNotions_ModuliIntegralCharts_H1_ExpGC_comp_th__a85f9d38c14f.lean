-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_comp_th__a85f9d38c14f
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_comp_th__a85f9d38c14f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:04.331712+00:00
-- url     : https://prove2.me/theorems/0a7c70da-c1fb-4a10-9632-d0b920b98de0
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GC comp th  a85f9d38c14f: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GC comp th  a85f9d38c14f
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GC comp th  a85f9d38c14f construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GC comp th  a85f9d38c14f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CocycleProductThree.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CocycleProductThree.lean#L50-L53

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

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_comp_th__a85f9d38c14f {T T' : Over Xo.X} (f : T' ⟶ T) (xs : Fin 3 → (T ⟶ Xo.univ.t.G)) (I : thK) :
    f.left ≫ thφ Xo.univ.t.G xs I = thφ Xo.univ.t.G (fun i => f ≫ xs i) I := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpGC».«comp_thφ» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_comp_th__a85f9d38c14f
