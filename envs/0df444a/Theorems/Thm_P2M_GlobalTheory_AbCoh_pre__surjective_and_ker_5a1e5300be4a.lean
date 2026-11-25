-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AbCoh_pre__surjective_and_ker_5a1e5300be4a
-- name    : P2M_GlobalTheory_AbCoh_pre__surjective_and_ker_5a1e5300be4a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:49:35.231931+00:00
-- url     : https://prove2.me/theorems/e7d3a25f-eb3c-40fc-ad49-cfc5a71d550e
-- title:
--   P2 M Global Theory Ab Coh pre  surjective and ker 5a1e5300be4a: P2 M Global Theory Ab Coh pre  surjective and ker 5a1e5300be4a
-- statement:
--   The P2 M Global Theory Ab Coh pre  surjective and ker 5a1e5300be4a construction uses the P2 M Global Theory Ab Coh pre  surjective and ker 5a1e5300be4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveDeformationAffineSections.lean#L69-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveDeformationAffineSections.lean#L69-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullSurjectiveAndKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveDeformationAffineSections
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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbCoh

theorem P2M_GlobalTheory_AbCoh_pre__surjective_and_ker_5a1e5300be4a : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) [IsAffineHom φ] [IsAffineHom φ₀], SmallExt t σ σ₀ → Flat s → ∀ U : AffOp X, Function.Surjective (preα φ s s' U) ∧ (∀ b, preα φ s s' U b = 0 ↔ ∃ c, b = t • c) ∧ Function.Surjective (preα φ₀ s s₀ U) ∧ ∀ b : (OAff s).obj U, preα φ₀ s s₀ U b = 0 ↔ t • b = 0 := by sorry

alias «GlobalTheory».«AbCoh».«preα_surjective_and_ker» := P2M_GlobalTheory_AbCoh_pre__surjective_and_ker_5a1e5300be4a
