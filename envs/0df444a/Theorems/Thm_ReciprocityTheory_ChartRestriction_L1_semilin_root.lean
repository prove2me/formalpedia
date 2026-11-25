-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_semilin_root
-- name    : ReciprocityTheory.ChartRestriction.L1.semilin_root
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:48:43.5292+00:00
-- url     : https://prove2.me/theorems/e8cdad03-1dbd-53cd-a11f-0b01e59bbd41
-- title:
--   L1: semilin root
-- statement:
--   The L1 construction uses the semilin root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/SemilinNormPowSubPow.lean#L57-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/SemilinNormPowSubPow.lean#L57-L72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SemilinNormPowSubPow
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
open Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]
omit [CompleteSpace K] [CharZero K]
open Polynomial

theorem ReciprocityTheory.ChartRestriction.L1.semilin_root {l : ℕ} (hR : ResClosed K l) {m : ℕ} (hm : 2 ≤ m) (a b : K) (ha : ‖a‖ ≤ 1)
    (hb : ‖b‖ ≤ 1) : ∃ x : K, ‖x‖ ≤ 1 ∧ ‖x ^ m + a * x + b‖ ≤ ‖(l : K)‖ := by sorry
