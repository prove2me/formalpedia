-- Prove2me | Theorems.Thm_PI_OddDualWeyl_MiscB_abel
-- name    : PI.OddDualWeyl.MiscB.abel
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:15:07.08626+00:00
-- url     : https://prove2.me/theorems/a0c89300-c346-5441-b88c-c7c9e11a0c4a
-- title:
--   Misc B: abel
-- statement:
--   The Misc B construction uses the abel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/DegreeBalance.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/DegreeBalance.lean#L12-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_DegreeBalance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.MiscB

theorem PI.OddDualWeyl.MiscB.abel (f : ℕ → ℕ) (hf : ∀ s, f (s + 1) ≤ f s) :
    ∀ n, ∑ s ∈ Finset.range n, (s + 1) * (f s - f (s + 1)) + n * f n = ∑ s ∈ Finset.range n, f s
  := by sorry
