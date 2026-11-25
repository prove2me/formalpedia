-- Prove2me | Theorems.Thm_P2M_GlobalTheory_JetLinSub_appTop_to__0f0c9eb1fee2
-- name    : P2M_GlobalTheory_JetLinSub_appTop_to__0f0c9eb1fee2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T18:41:23.336795+00:00
-- url     : https://prove2.me/theorems/5e63f78a-b8c0-5384-a7bc-bdfede84ad28
-- title:
--   P2 M Global Theory Jet Lin Sub app Top to  0f0c9eb1fee2: P2 M Global Theory Jet Lin Sub app Top to  0f0c9eb1fee2
-- statement:
--   The P2 M Global Theory Jet Lin Sub app Top to  0f0c9eb1fee2 construction uses the P2 M Global Theory Jet Lin Sub app Top to  0f0c9eb1fee2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/JetReadingLinearSubstitutionPoints.lean#L140-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/JetReadingLinearSubstitutionPoints.lean#L140-L144

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetLinSub

theorem P2M_GlobalTheory_JetLinSub_appTop_to__0f0c9eb1fee2 {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (a : R) :
    ((spMap f).appTop).hom (toΓ R a) = toΓ R' (f a) := by sorry

alias «GlobalTheory».«JetLinSub».«appTop_toΓ» := P2M_GlobalTheory_JetLinSub_appTop_to__0f0c9eb1fee2
