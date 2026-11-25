-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Ar_ProjCoord_pt_away__eq_854980b86607
-- name    : P2M_GlobalTheory_CompanionTheory_Ar_ProjCoord_pt_away__eq_854980b86607
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:05:30.695275+00:00
-- url     : https://prove2.me/theorems/78892c0f-1e60-5cd3-b20b-a3d70c117bbe
-- title:
--   P2 M Global Theory Companion Theory Ar Proj Coord pt away  eq 854980b86607: P2 M Global Theory Companion Theory Ar Proj Coord pt away  eq 854980b86607
-- statement:
--   The P2 M Global Theory Companion Theory Ar Proj Coord pt away  eq 854980b86607 construction uses the P2 M Global Theory Companion Theory Ar Proj Coord pt away  eq 854980b86607 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L127-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L127-L139

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.ProjCoord
open HomogeneousLocalization
variable {σ A Ω : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [Field Ω]

theorem P2M_GlobalTheory_CompanionTheory_Ar_ProjCoord_pt_away__eq_854980b86607 (ψ : A →+* Ω) {f g : A} {d e : ℕ} (hd : f ∈ 𝒜 d) (he : g ∈ 𝒜 e)
    (d0 : 0 < d) (e0 : 0 < e) (hf : ψ f ≠ 0) (hg : ψ g ≠ 0) :
    CptModel.pt (awayEval 𝒜 ψ f hf) ≫ Proj.awayι 𝒜 f hd d0 =
      CptModel.pt (awayEval 𝒜 ψ g hg) ≫ Proj.awayι 𝒜 g he e0 := by sorry

alias «GlobalTheory».«CompanionTheory».«Ar».«ProjCoord».«pt_awayι_eq» := P2M_GlobalTheory_CompanionTheory_Ar_ProjCoord_pt_away__eq_854980b86607
