-- Prove2me | Theorems.Thm_P2M_Formalism_CountingSumsFrames_ltr_of__7102e4470fc7
-- name    : P2M_Formalism_CountingSumsFrames_ltr_of__7102e4470fc7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:59.916394+00:00
-- url     : https://prove2.me/theorems/bb016d42-06fb-4fb6-8a70-8c594f3bc4db
-- title:
--   P2 M Formalism Counting Sums Frames ltr of  7102e4470fc7: P2 M Formalism Counting Sums Frames ltr of  7102e4470fc7
-- statement:
--   The P2 M Formalism Counting Sums Frames ltr of  7102e4470fc7 construction uses the P2 M Formalism Counting Sums Frames ltr of  7102e4470fc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L500-L502
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L500-L502

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]

theorem P2M_Formalism_CountingSumsFrames_ltr_of__7102e4470fc7 {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → ¬ fs v) : ltr fs m = m := by sorry

alias «Formalism».«CountingSumsFrames».«ltr_of'» := P2M_Formalism_CountingSumsFrames_ltr_of__7102e4470fc7
