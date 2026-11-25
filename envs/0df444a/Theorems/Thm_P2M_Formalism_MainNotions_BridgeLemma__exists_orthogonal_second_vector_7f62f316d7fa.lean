-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__exists_orthogonal_second_vector_7f62f316d7fa
-- name    : P2M_Formalism_MainNotions_BridgeLemma__exists_orthogonal_second_vector_7f62f316d7fa
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:21.223172+00:00
-- url     : https://prove2.me/theorems/1b056f7a-050f-46ae-b84e-3203fc89b15d
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  exists orthogonal second vector 7f62f316d7fa: P2 M Formalism Main Notions Bridge Lemma  exists orthogonal second vector 7f62f316d7fa
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  exists orthogonal second vector 7f62f316d7fa construction uses the P2 M Formalism Main Notions Bridge Lemma  exists orthogonal second vector 7f62f316d7fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L191-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L191-L278

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ExistsSmallMemFractionalIdeal
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
open NumberField NumberField.mixedEmbedding Formalism.HermitianLatticesTheory
open scoped nonZeroDivisors NNReal ENNReal

theorem P2M_Formalism_MainNotions_BridgeLemma__exists_orthogonal_second_vector_7f62f316d7fa (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L 2)
    (M : Submodule (𝓞 K) V) (hlat : Submodule.IsLattice K M) (hint : Formalism.HermitianLatticesTheory.IsIntegralLat h M)
    (huni : Formalism.HermitianLatticesTheory.dual h M = M) (x : V) (hx : x ∈ M) (hx0 : x ≠ 0) :
    ∃ y ∈ M, y ≠ 0 ∧ h x y = 0 ∧ ∀ φ : K →+* ℂ, ‖φ (h y y)‖ ≤ ‖φ (h x x)‖ * rootDiscriminant K := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«exists_orthogonal_second_vector» := P2M_Formalism_MainNotions_BridgeLemma__exists_orthogonal_second_vector_7f62f316d7fa
