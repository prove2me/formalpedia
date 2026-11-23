-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__planeMap_apply_alt_8549fdd1aaf1
-- name    : P2M_Formalism_MainNotions_BridgeLemma__planeMap_apply_alt_8549fdd1aaf1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:13:26.281084+00:00
-- url     : https://prove2.me/theorems/e84ca916-937a-4dc6-843d-f40fe387dd54
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  plane Map apply alt 8549fdd1aaf1: P2 M Formalism Main Notions Bridge Lemma  plane Map apply alt 8549fdd1aaf1
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  plane Map apply alt 8549fdd1aaf1 construction uses the P2 M Formalism Main Notions Bridge Lemma  plane Map apply alt 8549fdd1aaf1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L155-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L155-L157

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

theorem P2M_Formalism_MainNotions_BridgeLemma__planeMap_apply_alt_8549fdd1aaf1 (x y x' y' v : V) :
    planeMapAlt h x y x' y' v = (h x v / h x x) • x' + (h y v / h y y) • y' := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«planeMap_apply_alt» := P2M_Formalism_MainNotions_BridgeLemma__planeMap_apply_alt_8549fdd1aaf1
