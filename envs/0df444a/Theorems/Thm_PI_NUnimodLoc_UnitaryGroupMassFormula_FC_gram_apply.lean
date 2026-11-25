-- Prove2me | Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_gram_apply
-- name    : PI.NUnimodLoc.UnitaryGroupMassFormula.FC.gram_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:34:36.79633+00:00
-- url     : https://prove2.me/theorems/b53bbbfe-59b7-51f6-a41a-cfdf635b501a
-- title:
--   FC: gram apply
-- statement:
--   The FC construction uses the gram apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/FrameC.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/FrameC.lean#L45-L51

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

theorem PI.NUnimodLoc.UnitaryGroupMassFormula.FC.gram_apply (i j : Fin (2 * r + k + 1)) :
    ((Pm k r e f wf z0)ᴴ * Jm ε * Pm k r e f wf z0) i j =
      hJ ε (fcol k r e f wf z0 i) (fcol k r e f wf z0 j) := by sorry
