-- Prove2me | Theorems.Thm_P2M_PI_ZW_finsum_mem_le_finsum_mem__57f47eb1a398
-- name    : P2M_PI_ZW_finsum_mem_le_finsum_mem__57f47eb1a398
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:02:02.973742+00:00
-- url     : https://prove2.me/theorems/b7d27595-e745-4761-9cdc-17df86255f3b
-- title:
--   P2 M PI ZW finsum mem le finsum mem  57f47eb1a398: P2 M PI ZW finsum mem le finsum mem  57f47eb1a398
-- statement:
--   The P2 M PI ZW finsum mem le finsum mem  57f47eb1a398 construction uses the P2 M PI ZW finsum mem le finsum mem  57f47eb1a398 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/FinsumMemLeFinsumMem.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/FinsumMemLeFinsumMem.lean#L14-L17

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_FinsumMemLeFinsumMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ZW
open DirichletCharacter

theorem P2M_PI_ZW_finsum_mem_le_finsum_mem__57f47eb1a398 {s : Set ℂ} (f g : ℂ → ℝ) (hs : s.Finite) (h : ∀ x ∈ s, f x ≤ g x) :
    ∑ᶠ x ∈ s, f x ≤ ∑ᶠ x ∈ s, g x := by sorry

alias «PI».«ZW».«finsum_mem_le_finsum_mem'» := P2M_PI_ZW_finsum_mem_le_finsum_mem__57f47eb1a398
