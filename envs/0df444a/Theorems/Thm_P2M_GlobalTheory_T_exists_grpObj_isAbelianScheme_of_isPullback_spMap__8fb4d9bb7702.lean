-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_grpObj_isAbelianScheme_of_isPullback_spMap__8fb4d9bb7702
-- name    : P2M_GlobalTheory_T_exists_grpObj_isAbelianScheme_of_isPullback_spMap__8fb4d9bb7702
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:09:31.41989+00:00
-- url     : https://prove2.me/theorems/d69c5be4-03e3-4956-9073-7ff697288b24
-- title:
--   P2 M Global Theory T exists grp Obj is Abelian Scheme of is Pullback sp Map  8fb4d9bb7702: P2 M Global Theory T exists grp Obj is Abelian Scheme of is Pullback sp Map  8fb4d9bb7702
-- statement:
--   The P2 M Global Theory T exists grp Obj is Abelian Scheme of is Pullback sp Map  8fb4d9bb7702 construction uses the P2 M Global Theory T exists grp Obj is Abelian Scheme of is Pullback sp Map  8fb4d9bb7702 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGrpObjIsAbelianSchemeOfIsPullbackSpMapStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGrpObjIsAbelianSchemeOfIsPullbackSpMapStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGrpObjIsAbelianSchemeOfIsPullbackSpMap
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGrpObjIsAbelianSchemeOfIsPullbackSpMapStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_grpObj_isAbelianScheme_of_isPullback_spMap__8fb4d9bb7702 : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left), IsPullback φ s' A.hom (spMap σ) → ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by sorry

alias «GlobalTheory».«T».«exists_grpObj_isAbelianScheme_of_isPullback_spMap'» := P2M_GlobalTheory_T_exists_grpObj_isAbelianScheme_of_isPullback_spMap__8fb4d9bb7702
