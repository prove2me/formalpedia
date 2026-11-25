-- Prove2me | Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_frame_conj_iff
-- name    : PI.NUnimodLoc.UnitaryGroupMassFormula.FC.frame_conj_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:34:39.021189+00:00
-- url     : https://prove2.me/theorems/582fec44-4786-45a0-95f1-e39fb7f7eb2d
-- title:
--   FC: frame conj iff
-- statement:
--   The FC construction uses the frame conj iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/FrameC.lean#L196-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/FrameC.lean#L196-L252

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

theorem PI.NUnimodLoc.UnitaryGroupMassFormula.FC.frame_conj_iff {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} (hc : c ≠ 0) (hz : z0 = c • z)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (inUJ ε g ∧ InN ε e z g) ↔ Qm k r ε e f wf z0 * g * Pm k r e f wf z0 ∈ Nset k r := by sorry
