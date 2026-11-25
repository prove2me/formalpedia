-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__class_count_plane_bound_5fa37ee7825f
-- name    : P2M_Formalism_MainNotions_BridgeLemma__class_count_plane_bound_5fa37ee7825f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:01:27.417201+00:00
-- url     : https://prove2.me/theorems/be955132-df70-4f6c-acd8-6f7e353fdd0f
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  class count plane bound 5fa37ee7825f: P2 M Formalism Main Notions Bridge Lemma  class count plane bound 5fa37ee7825f
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  class count plane bound 5fa37ee7825f construction uses the P2 M Formalism Main Notions Bridge Lemma  class count plane bound 5fa37ee7825f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L279-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L279-L391

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Formalism.HermitianLatticesTheory Module

theorem P2M_Formalism_MainNotions_BridgeLemma__class_count_plane_bound_5fa37ee7825f (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) (V : Type)
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule (𝓞 K) V) (hs : h.IsSymm) (hL : IsOrthoLattice h L 2) (s : Finset (Submodule (𝓞 K) V))
    (hreps : Formalism.ThetaLiftIndependence.IsClassReps h L s) (B₁ B₂ : ℝ) (hint : ∀ M ∈ s, IsIntegralLat h M)
    (hshort : ∀ M ∈ s, ∃ x ∈ M, ∃ y ∈ M, x ≠ 0 ∧ y ≠ 0 ∧ h x y = 0 ∧
      ∀ φ : K →+* ℂ, ‖φ (h x x)‖ ≤ B₁ ∧ ‖φ (h y y)‖ ≤ B₂) :
    (s.card : ℝ) ≤ (1 + 2 * B₁) ^ (2 * finrank ℚ K) * (1 + 2 * B₂) ^ (2 * finrank ℚ K) *
      (B₁ * B₂) ^ (4 * finrank ℚ K) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«class_count_plane_bound» := P2M_Formalism_MainNotions_BridgeLemma__class_count_plane_bound_5fa37ee7825f
