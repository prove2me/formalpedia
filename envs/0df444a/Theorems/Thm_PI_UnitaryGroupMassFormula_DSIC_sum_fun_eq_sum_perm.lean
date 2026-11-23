-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_sum_fun_eq_sum_perm
-- name    : PI.UnitaryGroupMassFormula.DSIC.sum_fun_eq_sum_perm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:17.388242+00:00
-- url     : https://prove2.me/theorems/ea4f1f38-1cb9-4ca4-945d-7c8d6d190f10
-- title:
--   DSIC: sum fun eq sum perm
-- statement:
--   The DSIC construction uses the sum fun eq sum perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CentralCharacters/QuasiDeterminantConjInv.lean#L33-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CentralCharacters/QuasiDeterminantConjInv.lean#L33-L46

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_CentralScalar
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QuasiDeterminantConjInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DSIC
open Finset
open scoped Matrix

theorem PI.UnitaryGroupMassFormula.DSIC.sum_fun_eq_sum_perm {M : Type*} [AddCommMonoid M] {n : ℕ} (f : (Fin n → Fin n) → M)
    (hf : ∀ c, ¬ Function.Injective c → f c = 0) :
    ∑ c, f c = ∑ π : Equiv.Perm (Fin n), f π := by sorry
