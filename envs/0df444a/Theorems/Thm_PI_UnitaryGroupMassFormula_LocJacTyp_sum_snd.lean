-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_sum_snd
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.sum_snd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:33:05.255405+00:00
-- url     : https://prove2.me/theorems/17b9d2b0-c209-4154-bf17-54e081382c5e
-- title:
--   Loc Jac Typ: sum snd
-- statement:
--   The Loc Jac Typ construction uses the sum snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean#L52-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
open scoped Classical

theorem PI.UnitaryGroupMassFormula.LocJacTyp.sum_snd (r : ℕ) (f : Fin (r + 1) → ℝ) :
    ∑ q : UIdx r, f q.1.2 = ∑ j : Fin (r + 1), ((j : ℕ) : ℝ) * f j := by sorry
