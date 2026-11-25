-- Prove2me | Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_sylvester_le
-- name    : PI.AutLzFinite.SlopeTestRemainingChoices.sylvester_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:23:50.246338+00:00
-- url     : https://prove2.me/theorems/57346aed-6ee7-43c4-b4e5-f1c178f11f15
-- title:
--   Slope Test Remaining Choices: sylvester le
-- statement:
--   The Slope Test Remaining Choices construction uses the sylvester le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/SylvesterLe.lean#L19-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/SylvesterLe.lean#L19-L85

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_SylvesterLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Matrix

theorem PI.AutLzFinite.SlopeTestRemainingChoices.sylvester_le {n k : Type} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (J : Matrix n n ℂ) {p q : ℕ} (hJ : Formalism.UG.HasSignature J p q) (B : Matrix n k ℂ)
    (hB : Function.Injective B.mulVec)
    (hneg : ∀ v : k → ℂ, (star (B *ᵥ v) ⬝ᵥ (J *ᵥ (B *ᵥ v))).re ≤ 0) : Fintype.card k ≤ q := by sorry
