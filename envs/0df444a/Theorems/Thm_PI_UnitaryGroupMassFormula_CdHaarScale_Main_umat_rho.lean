-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_umat_rho
-- name    : PI.UnitaryGroupMassFormula.CdHaarScale.Main.umat_rho
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:37:17.679238+00:00
-- url     : https://prove2.me/theorems/5f464cb0-cf85-4110-a0d5-20fbb4f9258f
-- title:
--   Main: umat rho
-- statement:
--   The Main construction uses the umat rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarScaling/MapEqSelfOfIterate.lean#L109-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarScaling/MapEqSelfOfIterate.lean#L109-L111

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CdHaarScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarScaling_MapEqSelfOfIterate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CdHaarScale PI.UnitaryGroupMassFormula.CdHaarScale.Main

theorem PI.UnitaryGroupMassFormula.CdHaarScale.Main.umat_rho {n : ℕ} {ε : Fin n → Bool} (π : Fin n ≃ Fin n) (hπ : ∀ i, ε (π i) = ε i)
    (a : Formalism.REAL.UJ ε) :
    PI.CdHaarScale.umat (rho π hπ a) = reindex π π (PI.CdHaarScale.umat a) := by sorry
