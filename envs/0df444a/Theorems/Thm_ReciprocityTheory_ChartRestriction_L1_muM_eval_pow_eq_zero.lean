-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_muM_eval_pow_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.L1.muM_eval_pow_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:44:48.026547+00:00
-- url     : https://prove2.me/theorems/02ebd0fe-95d7-4bea-8bf6-c4b1d8054e30
-- title:
--   L1: mu M eval pow eq zero
-- statement:
--   The L1 construction uses the mu M eval pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/MuMEvalPowEqZero.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/MuMEvalPowEqZero.lean#L53-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
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
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]

theorem ReciprocityTheory.ChartRestriction.L1.muM_eval_pow_eq_zero {K : Type*} [Field K] [CharZero K] (n : ℕ) (hn : 0 < n) (hln : ¬ l ∣ n)
    (g : K) (hg : g ^ n = 1) (p : ℤ[X]) (hp : p.eval₂ (Int.castRingHom K) g = 0) :
    p.eval₂ (Int.castRingHom K) (g ^ l) = 0 := by sorry
