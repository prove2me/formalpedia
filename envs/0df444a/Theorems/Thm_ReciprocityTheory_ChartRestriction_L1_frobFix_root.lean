-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_frobFix_root
-- name    : ReciprocityTheory.ChartRestriction.L1.frobFix_root
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:43:32.328142+00:00
-- url     : https://prove2.me/theorems/382cf438-000c-4525-9d20-63339ce84f8c
-- title:
--   L1: frob Fix root
-- statement:
--   The L1 construction uses the frob Fix root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FrobFixNegOne.lean#L93-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FrobFixNegOne.lean#L93-L103

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FrobFixNegOne
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
variable {R : Type*} [CommRing R] (p : ℕ)
variable {p}

theorem ReciprocityTheory.ChartRestriction.L1.frobFix_root (hp : p.Prime) {x : R} {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n)
    (hx : x ^ n = 1) : FrobFix p x := by sorry
