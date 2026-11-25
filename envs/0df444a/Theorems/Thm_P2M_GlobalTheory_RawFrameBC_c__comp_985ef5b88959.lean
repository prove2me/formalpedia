-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RawFrameBC_c__comp_985ef5b88959
-- name    : P2M_GlobalTheory_RawFrameBC_c__comp_985ef5b88959
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:09:16.395799+00:00
-- url     : https://prove2.me/theorems/9cf92080-f758-47e5-8a82-64af043ec608
-- title:
--   P2 M Global Theory Raw Frame BC c  comp 985ef5b88959: P2 M Global Theory Raw Frame BC c  comp 985ef5b88959
-- statement:
--   The P2 M Global Theory Raw Frame BC c  comp 985ef5b88959 construction uses the P2 M Global Theory Raw Frame BC c  comp 985ef5b88959 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsRawChartFramesBaseChange.lean#L128-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsRawChartFramesBaseChange.lean#L128-L132

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsRawChartFramesBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.RawFrameBC
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ)

theorem P2M_GlobalTheory_RawFrameBC_c__comp_985ef5b88959 {T T' : Over Xo.X} (ρ : T' ⟶ T) (a b : T ⟶ Xo.univ.t.G) :
    cφ ![ρ ≫ a, ρ ≫ b] = fun I => ρ.left ≫ cφ ![a, b] I := by sorry

alias «GlobalTheory».«RawFrameBC».«cφ_comp» := P2M_GlobalTheory_RawFrameBC_c__comp_985ef5b88959
