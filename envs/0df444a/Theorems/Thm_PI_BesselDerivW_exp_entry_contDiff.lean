-- Prove2me | Theorems.Thm_PI_BesselDerivW_exp_entry_contDiff
-- name    : PI.BesselDerivW.exp_entry_contDiff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:59.962044+00:00
-- url     : https://prove2.me/theorems/6520d121-065f-401d-be8c-83139cc70aa0
-- title:
--   Bessel Deriv W: exp entry cont Diff
-- statement:
--   The Bessel Deriv W construction uses the exp entry cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselDerivatives/ExpSup.lean#L16-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselDerivatives/ExpSup.lean#L16-L42

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_ContDiffOnDirectionalDerivative
import Definitions.Def_Formalism_PeriodIntegrals_BesselDeriv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_ExpSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Matrix
noncomputable section
open PI PI.BesselDerivW
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open scoped Matrix.Norms.Operator

theorem PI.BesselDerivW.exp_entry_contDiff (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ContDiff ℝ ∞ (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) := by sorry
