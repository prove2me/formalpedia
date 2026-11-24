-- Prove2me | Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_pm_mulVec_eq_sum
-- name    : PI.NUnimodLoc.UnitaryGroupMassFormula.FC.pm_mulVec_eq_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:57:53.303118+00:00
-- url     : https://prove2.me/theorems/9fcd8ab8-f5be-40e2-a569-376d98ff998c
-- title:
--   FC: pm mul Vec eq sum
-- statement:
--   The FC construction uses the pm mul Vec eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/FrameC.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/FrameC.lean#L40-L43

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_FrameC
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
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula PI.NUnimodLoc.UnitaryGroupMassFormula.FC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW Formalism.REAL
variable {k r : ℕ}
variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem PI.NUnimodLoc.UnitaryGroupMassFormula.FC.pm_mulVec_eq_sum (c : Fin (2 * r + k + 1) → ℂ) :
    Pm k r e f wf z0 *ᵥ c = ∑ j, c j • fcol k r e f wf z0 j := by sorry
