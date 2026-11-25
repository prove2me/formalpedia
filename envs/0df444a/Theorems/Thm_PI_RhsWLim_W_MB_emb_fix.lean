-- Prove2me | Theorems.Thm_PI_RhsWLim_W_MB_emb_fix
-- name    : PI.RhsWLim.W.MB.emb_fix
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:06.596376+00:00
-- url     : https://prove2.me/theorems/c499e01c-13dd-427e-9998-3ab9a8626b7a
-- title:
--   MB: emb fix
-- statement:
--   The MB construction uses the emb fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/MBaseMem.lean#L260-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/MBaseMem.lean#L260-L263

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.MB
open PI.RhsWLim
variable {k r : ℕ}

theorem PI.RhsWLim.W.MB.emb_fix (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (hj : ¬ mid k r j) :
    embWb k r a *ᵥ bvec j = bvec j := by sorry
