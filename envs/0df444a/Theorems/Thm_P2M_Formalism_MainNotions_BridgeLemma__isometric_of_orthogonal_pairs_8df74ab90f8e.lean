-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__isometric_of_orthogonal_pairs_8df74ab90f8e
-- name    : P2M_Formalism_MainNotions_BridgeLemma__isometric_of_orthogonal_pairs_8df74ab90f8e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:33.001184+00:00
-- url     : https://prove2.me/theorems/94fd02a7-df9e-498e-8b8c-f356819abb22
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  isometric of orthogonal pairs 8df74ab90f8e: P2 M Formalism Main Notions Bridge Lemma  isometric of orthogonal pairs 8df74ab90f8e
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  isometric of orthogonal pairs 8df74ab90f8e construction uses the P2 M Formalism Main Notions Bridge Lemma  isometric of orthogonal pairs 8df74ab90f8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L233-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L233-L262

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K)

theorem P2M_Formalism_MainNotions_BridgeLemma__isometric_of_orthogonal_pairs_8df74ab90f8e (hs : h.IsSymm) (hfr : finrank K V = 2) (M M' : Submodule (𝓞 K) V)
    (hint : IsIntegralLat h M) (hint' : IsIntegralLat h M') (x y x' y' : V) (hx : x ∈ M) (hy : y ∈ M)
    (hx' : x' ∈ M') (hy' : y' ∈ M') (hxy : h x y = 0) (hxx : h x x ≠ 0) (hyy : h y y ≠ 0) (hxy' : h x' y' = 0)
    (hα : h x' x' = h x x) (hβ : h y' y' = h y y)
    (hN : M.comap (pairCoords (K := K) ((h x x)⁻¹ • x) ((h y y)⁻¹ • y)) =
      M'.comap (pairCoords (K := K) ((h x' x')⁻¹ • x') ((h y' y')⁻¹ • y'))) :
    ∃ g ∈ isom h, gmap g M = M' := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«isometric_of_orthogonal_pairs» := P2M_Formalism_MainNotions_BridgeLemma__isometric_of_orthogonal_pairs_8df74ab90f8e
