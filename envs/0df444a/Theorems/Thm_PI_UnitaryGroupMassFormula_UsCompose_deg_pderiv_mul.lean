-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_deg_pderiv_mul
-- name    : PI.UnitaryGroupMassFormula.UsCompose.deg_pderiv_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:42:38.934299+00:00
-- url     : https://prove2.me/theorems/7fd614ef-9594-4a8b-965f-2b5d0002ea57
-- title:
--   Us Compose: deg pderiv mul
-- statement:
--   The Us Compose construction uses the deg pderiv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/DegPderivMul.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/DegPderivMul.lean#L12-L14

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Lemmata_PartialDerivativeDegree_PderivTdSuccLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_DegPderivMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U

theorem PI.UnitaryGroupMassFormula.UsCompose.deg_pderiv_mul {σ : Type*} (i : σ) (q L : MvPolynomial σ ℂ) (hL : L.totalDegree ≤ 1) :
    (pderiv i q * L).totalDegree ≤ q.totalDegree := by sorry
