-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__eq_zero_of_inner_self_eq_zero_e038a7e1209d
-- name    : P2M_Formalism_MainNotions_BridgeLemma__eq_zero_of_inner_self_eq_zero_e038a7e1209d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:29.043605+00:00
-- url     : https://prove2.me/theorems/eb85a55f-2020-4258-808c-c8e2b1cca76d
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  eq zero of inner self eq zero e038a7e1209d: P2 M Formalism Main Notions Bridge Lemma  eq zero of inner self eq zero e038a7e1209d
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  eq zero of inner self eq zero e038a7e1209d construction uses the P2 M Formalism Main Notions Bridge Lemma  eq zero of inner self eq zero e038a7e1209d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L104-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L104-L126

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

theorem P2M_Formalism_MainNotions_BridgeLemma__eq_zero_of_inner_self_eq_zero_e038a7e1209d (hK : IsCMUnram K) (L : Submodule (𝓞 K) V) (hL : IsOrthoLattice h L 2) (v : V)
    (hv : h v v = 0) : v = 0 := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«eq_zero_of_inner_self_eq_zero» := P2M_Formalism_MainNotions_BridgeLemma__eq_zero_of_inner_self_eq_zero_e038a7e1209d
