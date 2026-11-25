-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_sv_sum
-- name    : PI.UnitaryGroupMassFormula.LCG.sv_sum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:56:22.813144+00:00
-- url     : https://prove2.me/theorems/66cd08c2-6894-4648-b1d9-c2c36ee6f8c3
-- title:
--   LCG: sv sum
-- statement:
--   The LCG construction uses the sv sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/IndexOf.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/IndexOf.lean#L22-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem PI.UnitaryGroupMassFormula.LCG.sv_sum {k : ℕ} (s : Fin k → E) (b : Fin k → Fin n → E) :
    sv (∑ a, starRingEnd E (s a) • b a) = ∑ a, s a • sv (b a) := by sorry
