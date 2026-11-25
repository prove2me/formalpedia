-- Prove2me | Theorems.Thm_UpperTheory_HF_rd_lower
-- name    : UpperTheory.HF.rd_lower
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:23:09.621266+00:00
-- url     : https://prove2.me/theorems/c9664e68-1d85-5dda-b9c8-3488b944f98e
-- title:
--   HF: rd lower
-- statement:
--   The HF construction uses the rd lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/RdLower.lean#L23-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/RdLower.lean#L23-L37

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RdLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.rd_lower :
    ∀ {φ : Frame} (H : HostAx φ), (6.7 : ℝ) < (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) ∧ (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) ≤ H.rd / Real.sqrt H.d ∧ 8 < H.rd / 2 ∧ 2 * 2 ^ φ.e ≤ 2 * φ.ord ∧ 2 * φ.ord ≤ 2 * φ.o * 2 ^ φ.e := by sorry
