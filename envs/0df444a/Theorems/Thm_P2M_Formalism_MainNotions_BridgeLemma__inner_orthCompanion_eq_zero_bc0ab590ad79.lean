-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_orthCompanion_eq_zero_bc0ab590ad79
-- name    : P2M_Formalism_MainNotions_BridgeLemma__inner_orthCompanion_eq_zero_bc0ab590ad79
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:34.460279+00:00
-- url     : https://prove2.me/theorems/e42d2c2f-7524-46bc-b47b-e5e7923ae429
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  inner orth Companion eq zero bc0ab590ad79: P2 M Formalism Main Notions Bridge Lemma  inner orth Companion eq zero bc0ab590ad79
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  inner orth Companion eq zero bc0ab590ad79 construction uses the P2 M Formalism Main Notions Bridge Lemma  inner orth Companion eq zero bc0ab590ad79 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L137-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L137-L141

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

theorem P2M_Formalism_MainNotions_BridgeLemma__inner_orthCompanion_eq_zero_bc0ab590ad79 (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x : V) :
    h x (orthCompanion h e x) = 0 := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«inner_orthCompanion_eq_zero» := P2M_Formalism_MainNotions_BridgeLemma__inner_orthCompanion_eq_zero_bc0ab590ad79
