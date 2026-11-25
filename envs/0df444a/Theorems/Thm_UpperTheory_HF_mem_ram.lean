-- Prove2me | Theorems.Thm_UpperTheory_HF_mem_ram
-- name    : UpperTheory.HF.mem_ram
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:45:38.738974+00:00
-- url     : https://prove2.me/theorems/02347a77-aae9-4d7c-a0d9-a5d0f618434c
-- title:
--   HF: mem ram
-- statement:
--   The HF construction uses the mem ram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/MemRam.lean#L10-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/MemRam.lean#L10-L92

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdFormula
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LayerBot
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.mem_ram :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → (l ∈ H.ram ↔ H.el l ≠ 1) ∧ (l ∈ H.ram ↔ l ∣ H.condE) ∧ (l ∈ H.ram ↔ H.vdH l ≠ 0) ∧ (l ∈ H.ram → 1 / 2 ≤ H.vdH l) ∧ (l ∈ H.ram → 1 - 1 / (H.el l : ℝ) ≤ H.vdH l) := by sorry
