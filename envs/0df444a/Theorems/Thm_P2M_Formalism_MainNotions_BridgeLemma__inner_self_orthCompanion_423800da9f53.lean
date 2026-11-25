-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_self_orthCompanion_423800da9f53
-- name    : P2M_Formalism_MainNotions_BridgeLemma__inner_self_orthCompanion_423800da9f53
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:52.504805+00:00
-- url     : https://prove2.me/theorems/3461875b-03b1-4362-8318-b6c0aa032f47
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  inner self orth Companion 423800da9f53: P2 M Formalism Main Notions Bridge Lemma  inner self orth Companion 423800da9f53
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  inner self orth Companion 423800da9f53 construction uses the P2 M Formalism Main Notions Bridge Lemma  inner self orth Companion 423800da9f53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L129-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L129-L135

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

theorem P2M_Formalism_MainNotions_BridgeLemma__inner_self_orthCompanion_423800da9f53 (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x : V) :
    h (orthCompanion h e x) (orthCompanion h e x) = h x x := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«inner_self_orthCompanion» := P2M_Formalism_MainNotions_BridgeLemma__inner_self_orthCompanion_423800da9f53
