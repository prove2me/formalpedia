-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_sum_orthonormal_pair_c303edb6b013
-- name    : P2M_Formalism_MainNotions_BridgeLemma__inner_sum_orthonormal_pair_c303edb6b013
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:54.444436+00:00
-- url     : https://prove2.me/theorems/c468084b-d9a5-4a22-a6c6-f60be124b9e5
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  inner sum orthonormal pair c303edb6b013: P2 M Formalism Main Notions Bridge Lemma  inner sum orthonormal pair c303edb6b013
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  inner sum orthonormal pair c303edb6b013 construction uses the P2 M Formalism Main Notions Bridge Lemma  inner sum orthonormal pair c303edb6b013 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L77-L83

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_TraceInnerPosOfOrthonormalPair
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
open NumberField Module Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem P2M_Formalism_MainNotions_BridgeLemma__inner_sum_orthonormal_pair_c303edb6b013 (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (a c : Fin 2 → K) :
    h (∑ i, a i • e i) (∑ j, c j • e j) = ∑ i, star (a i) * c i := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«inner_sum_orthonormal_pair» := P2M_Formalism_MainNotions_BridgeLemma__inner_sum_orthonormal_pair_c303edb6b013
