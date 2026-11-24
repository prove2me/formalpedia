-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_FrobField_norm_sq_sub_pow_le
-- name    : ReciprocityTheory.ChartRestriction.L1.FrobField.norm_sq_sub_pow_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:35:51.92322+00:00
-- url     : https://prove2.me/theorems/dd88f623-c4d3-496f-b895-1c1a00e4feaf
-- title:
--   Frob Field: norm sq sub pow le
-- statement:
--   The Frob Field construction uses the norm sq sub pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/SemilinNormPowSubPow.lean#L41-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/SemilinNormPowSubPow.lean#L41-L52

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

theorem ReciprocityTheory.ChartRestriction.L1.FrobField.norm_sq_sub_pow_le {l : ℕ} {σ : K →+* K} (h : FrobField K l σ) (x : K) (hx : ‖x‖ ≤ 1) :
    ‖σ (σ x) - x ^ (l ^ 2)‖ ≤ ‖(l : K)‖ := by sorry
