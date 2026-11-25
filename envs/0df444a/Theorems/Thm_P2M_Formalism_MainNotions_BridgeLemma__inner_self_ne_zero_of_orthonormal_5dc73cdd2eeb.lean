-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_self_ne_zero_of_orthonormal_5dc73cdd2eeb
-- name    : P2M_Formalism_MainNotions_BridgeLemma__inner_self_ne_zero_of_orthonormal_5dc73cdd2eeb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:39.656234+00:00
-- url     : https://prove2.me/theorems/e3dfeaa1-aa4f-47c8-b1ab-099a260f3ce8
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  inner self ne zero of orthonormal 5dc73cdd2eeb: P2 M Formalism Main Notions Bridge Lemma  inner self ne zero of orthonormal 5dc73cdd2eeb
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  inner self ne zero of orthonormal 5dc73cdd2eeb construction uses the P2 M Formalism Main Notions Bridge Lemma  inner self ne zero of orthonormal 5dc73cdd2eeb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L151-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L151-L172

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

theorem P2M_Formalism_MainNotions_BridgeLemma__inner_self_ne_zero_of_orthonormal_5dc73cdd2eeb (hcm : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x : V) (hx : x ≠ 0) : h x x ≠ 0 := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«inner_self_ne_zero_of_orthonormal» := P2M_Formalism_MainNotions_BridgeLemma__inner_self_ne_zero_of_orthonormal_5dc73cdd2eeb
