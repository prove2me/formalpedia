-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RawChartGermBC_appTop_to__spMap_21b8af0e1797
-- name    : P2M_GlobalTheory_RawChartGermBC_appTop_to__spMap_21b8af0e1797
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:43.409396+00:00
-- url     : https://prove2.me/theorems/12310950-bec1-4d22-8aee-ca062942c96e
-- title:
--   P2 M Global Theory Raw Chart Germ BC app Top to  sp Map 21b8af0e1797: P2 M Global Theory Raw Chart Germ BC app Top to  sp Map 21b8af0e1797
-- statement:
--   The P2 M Global Theory Raw Chart Germ BC app Top to  sp Map 21b8af0e1797 construction uses the P2 M Global Theory Raw Chart Germ BC app Top to  sp Map 21b8af0e1797 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/RawChartBaseChangeRigGerm.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/RawChartBaseChangeRigGerm.lean#L42-L46

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LBPull
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_RawChartBaseChangeRigGerm
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RawChartGermBC
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')

theorem P2M_GlobalTheory_RawChartGermBC_appTop_to__spMap_21b8af0e1797 (a : S) : (spMap ψ).appTop.hom (toΓ S a) = toΓ S' (ψ a) := by sorry

alias «GlobalTheory».«RawChartGermBC».«appTop_toΓ_spMap» := P2M_GlobalTheory_RawChartGermBC_appTop_to__spMap_21b8af0e1797
