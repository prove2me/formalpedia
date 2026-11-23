-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__eq_sum_coords_orthonormal_pair_0215a3f94e35
-- name    : P2M_Formalism_MainNotions_BridgeLemma__eq_sum_coords_orthonormal_pair_0215a3f94e35
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:25.804272+00:00
-- url     : https://prove2.me/theorems/2fec5f3c-69ac-4d23-87a6-046865d0e7a2
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  eq sum coords orthonormal pair 0215a3f94e35: P2 M Formalism Main Notions Bridge Lemma  eq sum coords orthonormal pair 0215a3f94e35
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  eq sum coords orthonormal pair 0215a3f94e35 construction uses the P2 M Formalism Main Notions Bridge Lemma  eq sum coords orthonormal pair 0215a3f94e35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L95-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L95-L108

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ExistsSmallMemFractionalIdeal
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
open NumberField NumberField.mixedEmbedding Formalism.HermitianLatticesTheory
open scoped nonZeroDivisors NNReal ENNReal
variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V)

theorem P2M_Formalism_MainNotions_BridgeLemma__eq_sum_coords_orthonormal_pair_0215a3f94e35 (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (v : V) :
    v = h (e 0) v • e 0 + h (e 1) v • e 1 := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«eq_sum_coords_orthonormal_pair» := P2M_Formalism_MainNotions_BridgeLemma__eq_sum_coords_orthonormal_pair_0215a3f94e35
