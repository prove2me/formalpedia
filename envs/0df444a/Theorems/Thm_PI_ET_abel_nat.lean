-- Prove2me | Theorems.Thm_PI_ET_abel_nat
-- name    : PI.ET.abel_nat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:28:58.96621+00:00
-- url     : https://prove2.me/theorems/9cb08cd5-d70c-4b57-9d57-ee0286776718
-- title:
--   ET: abel nat
-- statement:
--   The ET construction uses the abel nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/PsumEqRange.lean#L23-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/PsumEqRange.lean#L23-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_PsumEqRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.ET

theorem PI.ET.abel_nat (a c : ℕ → ℝ) : ∀ (n : ℕ), (∀ i j, i ≤ j → j < n → a j ≤ a i) →
    (∀ k ≤ n, 0 ≤ ∑ i ∈ range k, c i) → ∀ t : ℝ, (∀ i < n, t ≤ a i) →
    t * ∑ i ∈ range n, c i ≤ ∑ i ∈ range n, a i * c i := by sorry
