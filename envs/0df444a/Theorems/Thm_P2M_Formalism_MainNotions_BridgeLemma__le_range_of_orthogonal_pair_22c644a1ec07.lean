-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__le_range_of_orthogonal_pair_22c644a1ec07
-- name    : P2M_Formalism_MainNotions_BridgeLemma__le_range_of_orthogonal_pair_22c644a1ec07
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:59:50.783892+00:00
-- url     : https://prove2.me/theorems/776882b5-21f2-4579-a96a-87b4cd997fbc
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  le range of orthogonal pair 22c644a1ec07: P2 M Formalism Main Notions Bridge Lemma  le range of orthogonal pair 22c644a1ec07
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  le range of orthogonal pair 22c644a1ec07 construction uses the P2 M Formalism Main Notions Bridge Lemma  le range of orthogonal pair 22c644a1ec07 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L184-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L184-L195

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

theorem P2M_Formalism_MainNotions_BridgeLemma__le_range_of_orthogonal_pair_22c644a1ec07 (hs : h.IsSymm) (hfr : finrank K V = 2) (M : Submodule (𝓞 K) V)
    (hint : IsIntegralLat h M) (x y : V) (hx : x ∈ M) (hy : y ∈ M) (hxy : h x y = 0) (hxx : h x x ≠ 0)
    (hyy : h y y ≠ 0) : M ≤ LinearMap.range (pairCoords (K := K) ((h x x)⁻¹ • x) ((h y y)⁻¹ • y)) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«le_range_of_orthogonal_pair» := P2M_Formalism_MainNotions_BridgeLemma__le_range_of_orthogonal_pair_22c644a1ec07
