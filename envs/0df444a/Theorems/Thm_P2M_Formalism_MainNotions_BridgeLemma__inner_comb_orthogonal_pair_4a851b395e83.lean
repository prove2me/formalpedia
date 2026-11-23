-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_comb_orthogonal_pair_4a851b395e83
-- name    : P2M_Formalism_MainNotions_BridgeLemma__inner_comb_orthogonal_pair_4a851b395e83
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:09.550081+00:00
-- url     : https://prove2.me/theorems/de9105c2-cd0e-4d46-b4f2-921a1fb1cea8
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  inner comb orthogonal pair 4a851b395e83: P2 M Formalism Main Notions Bridge Lemma  inner comb orthogonal pair 4a851b395e83
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  inner comb orthogonal pair 4a851b395e83 construction uses the P2 M Formalism Main Notions Bridge Lemma  inner comb orthogonal pair 4a851b395e83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L98-L102

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

theorem P2M_Formalism_MainNotions_BridgeLemma__inner_comb_orthogonal_pair_4a851b395e83 (x y : V) (hxy : h x y = 0) (hyx : h y x = 0) (a c a' c' : K) :
    h (a • x + c • y) (a' • x + c' • y) = star a * a' * h x x + star c * c' * h y y := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«inner_comb_orthogonal_pair» := P2M_Formalism_MainNotions_BridgeLemma__inner_comb_orthogonal_pair_4a851b395e83
