-- Prove2me | Theorems.Thm_P2M_GlobalTheory_NabLinear_appTop_to__e0b53a85c105
-- name    : P2M_GlobalTheory_NabLinear_appTop_to__e0b53a85c105
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:54:06.579648+00:00
-- url     : https://prove2.me/theorems/8490abe6-4073-4133-8a64-9638f126acb4
-- title:
--   P2 M Global Theory Nab Linear app Top to  e0b53a85c105: P2 M Global Theory Nab Linear app Top to  e0b53a85c105
-- statement:
--   The P2 M Global Theory Nab Linear app Top to  e0b53a85c105 construction uses the P2 M Global Theory Nab Linear app Top to  e0b53a85c105 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ConnectionLinearInSection.lean#L115-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ConnectionLinearInSection.lean#L115-L119

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThExpBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ConnectionLinearInSection
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open GlobalTheory GlobalTheory.NabLinear

theorem P2M_GlobalTheory_NabLinear_appTop_to__e0b53a85c105 {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    ((spMap f).appTop).hom (toΓ A a) = toΓ B (f a) := by sorry

alias «GlobalTheory».«NabLinear».«appTop_toΓ» := P2M_GlobalTheory_NabLinear_appTop_to__e0b53a85c105
