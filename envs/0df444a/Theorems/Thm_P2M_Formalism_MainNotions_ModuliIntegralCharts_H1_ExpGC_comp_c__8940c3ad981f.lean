-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_comp_c__8940c3ad981f
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_comp_c__8940c3ad981f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:04:19.193014+00:00
-- url     : https://prove2.me/theorems/b4e817b2-147c-4750-af52-042206c9c72c
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GC comp c  8940c3ad981f: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GC comp c  8940c3ad981f
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GC comp c  8940c3ad981f construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GC comp c  8940c3ad981f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CocycleProductThree.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CocycleProductThree.lean#L45-L48

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

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_comp_c__8940c3ad981f {T T' : Over Xo.X} (f : T' ⟶ T) {n : ℕ} (xs : Fin n → (T ⟶ Xo.univ.t.G)) (I : ULift (Finset (Fin n))) :
    f.left ≫ cφ xs I = cφ (fun i => f ≫ xs i) I := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpGC».«comp_cφ» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_comp_c__8940c3ad981f
