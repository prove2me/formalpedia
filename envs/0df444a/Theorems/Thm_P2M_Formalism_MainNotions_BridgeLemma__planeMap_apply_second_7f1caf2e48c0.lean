-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__planeMap_apply_second_7f1caf2e48c0
-- name    : P2M_Formalism_MainNotions_BridgeLemma__planeMap_apply_second_7f1caf2e48c0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:59:58.445323+00:00
-- url     : https://prove2.me/theorems/08f99345-c4f6-4cd1-8cc0-9ee2d94e1fcc
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  plane Map apply second 7f1caf2e48c0: P2 M Formalism Main Notions Bridge Lemma  plane Map apply second 7f1caf2e48c0
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  plane Map apply second 7f1caf2e48c0 construction uses the P2 M Formalism Main Notions Bridge Lemma  plane Map apply second 7f1caf2e48c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L229-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L229-L231

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

theorem P2M_Formalism_MainNotions_BridgeLemma__planeMap_apply_second_7f1caf2e48c0 (x y x' y' : V) (hxy : h x y = 0) (hyy : h y y ≠ 0) :
    planeMapAlt h x y x' y' y = y' := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«planeMap_apply_second» := P2M_Formalism_MainNotions_BridgeLemma__planeMap_apply_second_7f1caf2e48c0
