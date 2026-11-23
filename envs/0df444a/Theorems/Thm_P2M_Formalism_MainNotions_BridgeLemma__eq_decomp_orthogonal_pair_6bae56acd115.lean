-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__eq_decomp_orthogonal_pair_6bae56acd115
-- name    : P2M_Formalism_MainNotions_BridgeLemma__eq_decomp_orthogonal_pair_6bae56acd115
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:16:38.176267+00:00
-- url     : https://prove2.me/theorems/c5913d14-95b4-4dea-ad8d-b5bc8b3b6588
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  eq decomp orthogonal pair 6bae56acd115: P2 M Formalism Main Notions Bridge Lemma  eq decomp orthogonal pair 6bae56acd115
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  eq decomp orthogonal pair 6bae56acd115 construction uses the P2 M Formalism Main Notions Bridge Lemma  eq decomp orthogonal pair 6bae56acd115 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L133-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L133-L150

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

theorem P2M_Formalism_MainNotions_BridgeLemma__eq_decomp_orthogonal_pair_6bae56acd115 (hs : h.IsSymm) (hfr : finrank K V = 2) (x y : V) (hxy : h x y = 0) (hxx : h x x ≠ 0)
    (hyy : h y y ≠ 0) (v : V) : v = (h x v / h x x) • x + (h y v / h y y) • y := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«eq_decomp_orthogonal_pair» := P2M_Formalism_MainNotions_BridgeLemma__eq_decomp_orthogonal_pair_6bae56acd115
