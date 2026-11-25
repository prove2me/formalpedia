-- Prove2me | Theorems.Thm_PI_ParahoricIdxZ_W_card_gt_one
-- name    : PI.ParahoricIdxZ.W.card_gt_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:47.280304+00:00
-- url     : https://prove2.me/theorems/5f91d659-7e39-4f3e-ba32-42c375ee37d8
-- title:
--   W: card gt one
-- statement:
--   The W construction uses the card gt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/Development.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/Development.lean#L37-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ParahoricIdxZ
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Finset
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W

theorem PI.ParahoricIdxZ.W.card_gt_one (F : Type) [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O)
    (hloc : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) [Finite (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)] :
    1 < Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) := by sorry
