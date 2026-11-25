-- Prove2me | Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_conj_form
-- name    : PI.NUnimodLoc.UnitaryGroupMassFormula.FC.conj_form
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:34:30.161646+00:00
-- url     : https://prove2.me/theorems/480824b8-c0ca-46fa-a6fc-2d33b039b263
-- title:
--   FC: conj form
-- statement:
--   The FC construction uses the conj form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/FrameC.lean#L162-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/FrameC.lean#L162-L176

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
variable (hF : IsFrameJ ε e f wf z0)
include hF

theorem PI.NUnimodLoc.UnitaryGroupMassFormula.FC.conj_form (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (Qm k r ε e f wf z0 * g * Pm k r e f wf z0)ᴴ * Hpk k r * (Qm k r ε e f wf z0 * g * Pm k r e f wf z0) =
      (Pm k r e f wf z0)ᴴ * (gᴴ * Jm ε * g) * Pm k r e f wf z0 := by sorry
