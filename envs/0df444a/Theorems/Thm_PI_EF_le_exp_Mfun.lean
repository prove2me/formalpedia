-- Prove2me | Theorems.Thm_PI_EF_le_exp_Mfun
-- name    : PI.EF.le_exp_Mfun
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:56.585847+00:00
-- url     : https://prove2.me/theorems/8a473fa1-6444-4d57-b75e-ae29d3fc105d
-- title:
--   EF: le exp Mfun
-- statement:
--   The EF construction uses the le exp Mfun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/HalfLeNormLentCtr.lean#L156-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/HalfLeNormLentCtr.lean#L156-L164

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]

theorem PI.EF.le_exp_Mfun {A C : ℝ} (hC : 0 < C) (N : ℕ) [NeZero N] (t : ℝ) :
    2 * C * (4 * (N * (|t| + 2))) ^ A ≤ Real.exp (Mfun A C N t) := by sorry
