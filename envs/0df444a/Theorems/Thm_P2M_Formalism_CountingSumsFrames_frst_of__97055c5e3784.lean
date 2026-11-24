-- Prove2me | Theorems.Thm_P2M_Formalism_CountingSumsFrames_frst_of__97055c5e3784
-- name    : P2M_Formalism_CountingSumsFrames_frst_of__97055c5e3784
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:12.828091+00:00
-- url     : https://prove2.me/theorems/caa26aa4-77db-4b71-9f92-fbe5fa5a3aff
-- title:
--   P2 M Formalism Counting Sums Frames frst of  97055c5e3784: P2 M Formalism Counting Sums Frames frst of  97055c5e3784
-- statement:
--   The P2 M Formalism Counting Sums Frames frst of  97055c5e3784 construction uses the P2 M Formalism Counting Sums Frames frst of  97055c5e3784 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L495-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L495-L499

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

theorem P2M_Formalism_CountingSumsFrames_frst_of__97055c5e3784 {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → ¬ fs v) : frst fs m = 0 := by sorry

alias «Formalism».«CountingSumsFrames».«frst_of'» := P2M_Formalism_CountingSumsFrames_frst_of__97055c5e3784
