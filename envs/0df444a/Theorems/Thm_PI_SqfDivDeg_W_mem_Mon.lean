-- Prove2me | Theorems.Thm_PI_SqfDivDeg_W_mem_Mon
-- name    : PI.SqfDivDeg.W.mem_Mon
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:52.724649+00:00
-- url     : https://prove2.me/theorems/a8708c7a-06f4-4150-bf7e-31b1153c5454
-- title:
--   W: mem Mon
-- statement:
--   The W construction uses the mem Mon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/MonicFintype.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/MonicFintype.lean#L19-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqfLab
import Definitions.Def_Formalism_PeriodIntegrals_SqfDivDeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W

theorem PI.SqfDivDeg.W.mem_Mon {g : ℕ} [Fact g.Prime] {n : ℕ} {p : (ZMod g)[X]} :
    p ∈ Mon g n ↔ p.Monic ∧ p.natDegree = n := by sorry
