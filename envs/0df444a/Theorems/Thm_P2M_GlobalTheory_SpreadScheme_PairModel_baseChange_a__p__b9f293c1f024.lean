-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SpreadScheme_PairModel_baseChange_a__p__b9f293c1f024
-- name    : P2M_GlobalTheory_SpreadScheme_PairModel_baseChange_a__p__b9f293c1f024
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:13:49.964158+00:00
-- url     : https://prove2.me/theorems/8ada4b6e-1059-5b98-9657-3723c30e3235
-- title:
--   P2 M Global Theory Spread Scheme Pair Model base Change a  p  b9f293c1f024: P2 M Global Theory Spread Scheme Pair Model base Change a  p  b9f293c1f024
-- statement:
--   The P2 M Global Theory Spread Scheme Pair Model base Change a  p  b9f293c1f024 construction uses the P2 M Global Theory Spread Scheme Pair Model base Change a  p  b9f293c1f024 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SchemeDescendsToSubalgebra.lean#L183-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SchemeDescendsToSubalgebra.lean#L183-L185

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SchemeDescendsToSubalgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SpreadScheme
open GlobalTheory.Spread GlobalTheory.GlueModels
attribute [instance] PairModel.lfp PairModel.qs PairModel.qc PairModel.opn PairModel.qca
variable {S S₁ S₀ U T : Scheme.{0}} {f : S ⟶ S₀} {p : U ⟶ S} {a : T ⟶ U}

theorem P2M_GlobalTheory_SpreadScheme_PairModel_baseChange_a__p__b9f293c1f024 (M : PairModel f p a) (σ : S ⟶ S₁) (g : S₁ ⟶ S₀) (e : σ ≫ g = f) :
    (M.baseChange σ g e).a₀ ≫ (M.baseChange σ g e).p₀ = pullback.snd (M.a₀ ≫ M.p₀) g := by sorry

alias «GlobalTheory».«SpreadScheme».«PairModel».«baseChange_a₀_p₀» := P2M_GlobalTheory_SpreadScheme_PairModel_baseChange_a__p__b9f293c1f024
