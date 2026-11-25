-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__scaledFreeModule_le_comap_78a7cdd93a48
-- name    : P2M_Formalism_MainNotions_BridgeLemma__scaledFreeModule_le_comap_78a7cdd93a48
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:59:49.566339+00:00
-- url     : https://prove2.me/theorems/96d3668f-63f7-43e7-b77d-7743153a3456
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  scaled Free Module le comap 78a7cdd93a48: P2 M Formalism Main Notions Bridge Lemma  scaled Free Module le comap 78a7cdd93a48
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  scaled Free Module le comap 78a7cdd93a48 construction uses the P2 M Formalism Main Notions Bridge Lemma  scaled Free Module le comap 78a7cdd93a48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L197-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L197-L214

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

theorem P2M_Formalism_MainNotions_BridgeLemma__scaledFreeModule_le_comap_78a7cdd93a48 (M : Submodule (𝓞 K) V) (x y : V) (hx : x ∈ M) (hy : y ∈ M) (a b : 𝓞 K)
    (ha : algebraMap (𝓞 K) K a = h x x) (hb : algebraMap (𝓞 K) K b = h y y) (hxx : h x x ≠ 0) (hyy : h y y ≠ 0) :
    scaledFreeModule K (a * b) ≤ M.comap (pairCoords (K := K) ((h x x)⁻¹ • x) ((h y y)⁻¹ • y)) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«scaledFreeModule_le_comap» := P2M_Formalism_MainNotions_BridgeLemma__scaledFreeModule_le_comap_78a7cdd93a48
