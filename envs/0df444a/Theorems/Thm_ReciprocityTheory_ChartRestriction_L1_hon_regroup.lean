-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hon_regroup
-- name    : ReciprocityTheory.ChartRestriction.L1.hon_regroup
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:45:01.389189+00:00
-- url     : https://prove2.me/theorems/248a6e57-4dd7-4361-8803-ff6b4674cf37
-- title:
--   L1: hon regroup
-- statement:
--   The L1 construction uses the hon regroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonH.lean#L15-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonH.lean#L15-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [Field K]

theorem ReciprocityTheory.ChartRestriction.L1.hon_regroup (τ : K →+* K) (π : K) (c t w : ℕ → K) (M : ℕ) (hM : 1 ≤ M)
    (hw : ∀ m, M ≤ m → w m = 0) (ht0 : t 0 = 1)
    (ht : ∀ n, 2 ≤ n → π * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i))) :
    ∑ i ∈ Finset.range M, t i * (π * w i - ∑ j ∈ Finset.range M, (τ ^ i) (c j) * w (i + j + 1))
      = π * w 0 - (c 0 - π * t 1) * w 1 := by sorry
