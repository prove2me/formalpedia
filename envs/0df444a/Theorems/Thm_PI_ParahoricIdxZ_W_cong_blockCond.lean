-- Prove2me | Theorems.Thm_PI_ParahoricIdxZ_W_cong_blockCond
-- name    : PI.ParahoricIdxZ.W.cong_blockCond
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:42.28379+00:00
-- url     : https://prove2.me/theorems/f25fde6e-9e45-5344-9a02-9ab33260287e
-- title:
--   W: cong block Cond
-- statement:
--   The W construction uses the cong block Cond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ThetaInjective.lean#L117-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ThetaInjective.lean#L117-L178

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)
variable {ϖ}

theorem PI.ParahoricIdxZ.W.cong_blockCond (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hloc : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) {a t : ℕ}
    {J' : Subgroup (GL (Fin a) F)} (hKJ : Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J')
    {g : GL (Fin (a + t)) F} (hg : g ∈ Formalism.DoubleCosetMeasures.congSub O ϖ (a + t)) : blockCond O ϖ J' g := by sorry
