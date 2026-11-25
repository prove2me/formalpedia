-- Prove2me | Theorems.Thm_PI_RhsWLim_W_PH_subst_R
-- name    : PI.RhsWLim.W.PH.subst_R
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:27:23.033846+00:00
-- url     : https://prove2.me/theorems/b4635f42-629d-4035-98b8-858086e7a1bf
-- title:
--   PH: subst R
-- statement:
--   The PH construction uses the subst R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PolarHyp.lean#L93-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PolarHyp.lean#L93-L147

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PolarHyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.PH

theorem PI.RhsWLim.W.PH.subst_R (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (X : ℝ → ℝ≥0∞)
    (hX : ∀ R ∈ Ioo 0 (Real.sqrt (T * T')), X R = 0) :
    ∫⁻ R in Ioi 0, X R = ∫⁻ ρ in Ioi 0,
      ENNReal.ofReal (|T * ρ / Real.sqrt (T * (ρ ^ 2 + T'))|) * X (Real.sqrt (T * (ρ ^ 2 + T'))) := by sorry
