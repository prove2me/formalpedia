-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_finset_model_of_isAffine__8386d6febae7
-- name    : P2M_GlobalTheory_T_exists_finset_model_of_isAffine__8386d6febae7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:34.038426+00:00
-- url     : https://prove2.me/theorems/7f10c8ae-079e-46f1-89da-7b2ba56b879e
-- title:
--   P2 M Global Theory T exists finset model of is Affine  8386d6febae7: P2 M Global Theory T exists finset model of is Affine  8386d6febae7
-- statement:
--   The P2 M Global Theory T exists finset model of is Affine  8386d6febae7 construction uses the P2 M Global Theory T exists finset model of is Affine  8386d6febae7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFinsetModelOfIsAffineStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFinsetModelOfIsAffineStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFinsetModelOfIsAffine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFinsetModelOfIsAffineStatement
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

theorem P2M_GlobalTheory_T_exists_finset_model_of_isAffine__8386d6febae7 : ∀ (K : Type) [Field K] (X : Over (Sp K)), IsAffine X.left → LocallyOfFiniteType X.hom → ∃ s : Finset K, ∀ (k : Type) [Field k] (β : k →+* K), (s : Set K) ⊆ Set.range β → ∃ (X₀ : Over (Sp k)) (φ : X.left ⟶ X₀.left), IsPullback φ X.hom X₀.hom (spMap β) := by sorry

alias «GlobalTheory».«T».«exists_finset_model_of_isAffine'» := P2M_GlobalTheory_T_exists_finset_model_of_isAffine__8386d6febae7
