-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__pairCoords_apply_ef037467d414
-- name    : P2M_Formalism_MainNotions_BridgeLemma__pairCoords_apply_ef037467d414
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:17:49.236973+00:00
-- url     : https://prove2.me/theorems/365902bd-0693-4d81-a869-d013912130a6
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  pair Coords apply ef037467d414: P2 M Formalism Main Notions Bridge Lemma  pair Coords apply ef037467d414
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  pair Coords apply ef037467d414 construction uses the P2 M Formalism Main Notions Bridge Lemma  pair Coords apply ef037467d414 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L181-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L181-L182

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

theorem P2M_Formalism_MainNotions_BridgeLemma__pairCoords_apply_ef037467d414 (x₁ y₁ : V) (p : Fin 2 → 𝓞 K) : pairCoords x₁ y₁ p = p 0 • x₁ + p 1 • y₁ := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«pairCoords_apply» := P2M_Formalism_MainNotions_BridgeLemma__pairCoords_apply_ef037467d414
