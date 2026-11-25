-- Prove2me | Theorems.Thm_P2M_PI_ZW_finsum_mem_le_of_subset__d846247134c2
-- name    : P2M_PI_ZW_finsum_mem_le_of_subset__d846247134c2
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:01:39.23782+00:00
-- url     : https://prove2.me/theorems/fd147cf8-ce93-512f-987e-c40bc6f6ce6c
-- title:
--   P2 M PI ZW finsum mem le of subset  d846247134c2: P2 M PI ZW finsum mem le of subset  d846247134c2
-- statement:
--   The P2 M PI ZW finsum mem le of subset  d846247134c2 construction uses the P2 M PI ZW finsum mem le of subset  d846247134c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/FinsumMemLeFinsumMem.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/FinsumMemLeFinsumMem.lean#L9-L12

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

theorem P2M_PI_ZW_finsum_mem_le_of_subset__d846247134c2 {s t : Set ℂ} (g : ℂ → ℝ) (hg : ∀ x, 0 ≤ g x) (ht : t.Finite)
    (hst : s ⊆ t) : ∑ᶠ x ∈ s, g x ≤ ∑ᶠ x ∈ t, g x := by sorry

alias «PI».«ZW».«finsum_mem_le_of_subset'» := P2M_PI_ZW_finsum_mem_le_of_subset__d846247134c2
