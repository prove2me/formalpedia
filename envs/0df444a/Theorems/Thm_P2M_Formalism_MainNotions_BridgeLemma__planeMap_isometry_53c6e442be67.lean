-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__planeMap_isometry_53c6e442be67
-- name    : P2M_Formalism_MainNotions_BridgeLemma__planeMap_isometry_53c6e442be67
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:21.203623+00:00
-- url     : https://prove2.me/theorems/dc20a84d-ae7a-40f0-9c96-3f85eb92c193
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  plane Map isometry 53c6e442be67: P2 M Formalism Main Notions Bridge Lemma  plane Map isometry 53c6e442be67
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  plane Map isometry 53c6e442be67 construction uses the P2 M Formalism Main Notions Bridge Lemma  plane Map isometry 53c6e442be67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L168-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L168-L175

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

theorem P2M_Formalism_MainNotions_BridgeLemma__planeMap_isometry_53c6e442be67 (hs : h.IsSymm) (hfr : finrank K V = 2) (x y x' y' : V) (hxy : h x y = 0) (hxx : h x x ≠ 0)
    (hyy : h y y ≠ 0) (hxy' : h x' y' = 0) (hα : h x' x' = h x x) (hβ : h y' y' = h y y) (u v : V) :
    h (planeMapAlt h x y x' y' u) (planeMapAlt h x y x' y' v) = h u v := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«planeMap_isometry» := P2M_Formalism_MainNotions_BridgeLemma__planeMap_isometry_53c6e442be67
