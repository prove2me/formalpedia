-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_orthCompanion_symm_be982e5d4152
-- name    : P2M_Formalism_MainNotions_BridgeLemma__inner_orthCompanion_symm_be982e5d4152
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:26.828801+00:00
-- url     : https://prove2.me/theorems/967d7749-75eb-4992-a957-b26797a84a7e
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  inner orth Companion symm be982e5d4152: P2 M Formalism Main Notions Bridge Lemma  inner orth Companion symm be982e5d4152
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  inner orth Companion symm be982e5d4152 construction uses the P2 M Formalism Main Notions Bridge Lemma  inner orth Companion symm be982e5d4152 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L183-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L183-L189

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

theorem P2M_Formalism_MainNotions_BridgeLemma__inner_orthCompanion_symm_be982e5d4152 {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V) (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x v : V) :
    h v (orthCompanion h e x) = star (h (orthCompanion h e x) v) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«inner_orthCompanion_symm» := P2M_Formalism_MainNotions_BridgeLemma__inner_orthCompanion_symm_be982e5d4152
