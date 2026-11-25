-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__orthCompanion_inner_apply_9c68e5cead4d
-- name    : P2M_Formalism_MainNotions_BridgeLemma__orthCompanion_inner_apply_9c68e5cead4d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:59:39.614655+00:00
-- url     : https://prove2.me/theorems/b141eec5-e335-48c7-a847-22e55f1003e6
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  orth Companion inner apply 9c68e5cead4d: P2 M Formalism Main Notions Bridge Lemma  orth Companion inner apply 9c68e5cead4d
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  orth Companion inner apply 9c68e5cead4d construction uses the P2 M Formalism Main Notions Bridge Lemma  orth Companion inner apply 9c68e5cead4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L120-L123

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

theorem P2M_Formalism_MainNotions_BridgeLemma__orthCompanion_inner_apply_9c68e5cead4d (x v : V) :
    h (orthCompanion h e x) v = -(h (e 1) x) * h (e 0) v + h (e 0) x * h (e 1) v := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«orthCompanion_inner_apply» := P2M_Formalism_MainNotions_BridgeLemma__orthCompanion_inner_apply_9c68e5cead4d
