-- Prove2me | Theorems.Thm_PI_EF_Mfun_le
-- name    : PI.EF.Mfun_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:20.065258+00:00
-- url     : https://prove2.me/theorems/a3bc3fdc-2616-453e-817e-b971356b2b9e
-- title:
--   EF: Mfun le
-- statement:
--   The EF construction uses the Mfun le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/HalfLeNormLentCtr.lean#L140-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/HalfLeNormLentCtr.lean#L140-L154

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

theorem PI.EF.Mfun_le {A C : ℝ} (hA : 0 < A) (N : ℕ) [NeZero N] (t : ℝ) :
    Mfun A C N t ≤ (2 * |Real.log (2 * C)| + 3 * A) * LL N t := by sorry
