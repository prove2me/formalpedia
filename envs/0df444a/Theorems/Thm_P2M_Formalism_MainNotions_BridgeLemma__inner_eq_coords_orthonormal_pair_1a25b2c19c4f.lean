-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_eq_coords_orthonormal_pair_1a25b2c19c4f
-- name    : P2M_Formalism_MainNotions_BridgeLemma__inner_eq_coords_orthonormal_pair_1a25b2c19c4f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:13:00.536982+00:00
-- url     : https://prove2.me/theorems/5f305017-f662-4256-8dea-88d062a82b3b
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  inner eq coords orthonormal pair 1a25b2c19c4f: P2 M Formalism Main Notions Bridge Lemma  inner eq coords orthonormal pair 1a25b2c19c4f
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  inner eq coords orthonormal pair 1a25b2c19c4f construction uses the P2 M Formalism Main Notions Bridge Lemma  inner eq coords orthonormal pair 1a25b2c19c4f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L110-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L110-L116

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

theorem P2M_Formalism_MainNotions_BridgeLemma__inner_eq_coords_orthonormal_pair_1a25b2c19c4f (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (u v : V) :
    h u v = star (h (e 0) u) * h (e 0) v + star (h (e 1) u) * h (e 1) v := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«inner_eq_coords_orthonormal_pair» := P2M_Formalism_MainNotions_BridgeLemma__inner_eq_coords_orthonormal_pair_1a25b2c19c4f
