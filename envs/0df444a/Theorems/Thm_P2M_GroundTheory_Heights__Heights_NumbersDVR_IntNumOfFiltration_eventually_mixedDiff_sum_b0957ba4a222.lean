-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumOfFiltration_eventually_mixedDiff_sum_b0957ba4a222
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumOfFiltration_eventually_mixedDiff_sum_b0957ba4a222
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:11.342501+00:00
-- url     : https://prove2.me/theorems/ab54273e-719a-4597-9dce-481cd44c238f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Int Num Of Filtration eventually mixed Diff sum b0957ba4a222: P2 M Ground Theory Heights  Heights Numbers DVR Int Num Of Filtration eventually mixed Dif
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Int Num Of Filtration eventually mixed Diff sum b0957ba4a222 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Int Num Of Filtration eventually mixed Diff sum b0957ba4a222 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumOfFiltration.lean#L9-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumOfFiltration.lean#L9-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumOfFiltration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumOfFiltration

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumOfFiltration_eventually_mixedDiff_sum_b0957ba4a222 (h1 : MixedDiffLinear.Statement)
    (h3 : EventualValueFacts.Statement) {K : Type} {n : ℕ} (bs : Fin n → K → ℤ)
    {α : Type*} (h : α → (K → ℤ) → ℤ) (s : α → K → ℤ) :
    ∀ l : List α, (∀ p ∈ l, ∃ c : ℤ, ∀ᶠ m in Filter.atTop, mixedDiff bs (h p) m = c) →
      ∀ᶠ m in Filter.atTop,
        mixedDiff bs (fun m => (l.map fun p => h p (m - s p)).sum) m =
          (l.map fun p => eventualValue (mixedDiff bs (h p))).sum := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IntNumOfFiltration».«eventually_mixedDiff_sum» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumOfFiltration_eventually_mixedDiff_sum_b0957ba4a222
