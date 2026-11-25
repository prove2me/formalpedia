-- Prove2me | Theorems.Thm_PI_StabPairsW_coefOf_UT
-- name    : PI.StabPairsW.coefOf_UT
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:27:59.815707+00:00
-- url     : https://prove2.me/theorems/b90cd031-69b1-4be9-ad10-cfac605995ba
-- title:
--   Stab Pairs W: coef Of UT
-- statement:
--   The Stab Pairs W construction uses the coef Of UT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/Forward.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/Forward.lean#L85-L90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}

theorem PI.StabPairsW.coefOf_UT (y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    (Matrix.of fun a b => coefOf (k := k) b (y b) a) ∈ UTset (r + 1) := by sorry
