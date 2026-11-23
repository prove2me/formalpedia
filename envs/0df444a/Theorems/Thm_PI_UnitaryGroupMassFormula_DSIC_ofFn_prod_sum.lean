-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_ofFn_prod_sum
-- name    : PI.UnitaryGroupMassFormula.DSIC.ofFn_prod_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:15.012946+00:00
-- url     : https://prove2.me/theorems/9ad0f256-0223-472b-b605-405be43d64a1
-- title:
--   DSIC: of Fn prod sum
-- statement:
--   The DSIC construction uses the of Fn prod sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CentralCharacters/QuasiDeterminantConjInv.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CentralCharacters/QuasiDeterminantConjInv.lean#L11-L19

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

theorem PI.UnitaryGroupMassFormula.DSIC.ofFn_prod_sum {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ (t : ℕ) (f : Fin t → ι → R),
      (List.ofFn fun k => ∑ c, f k c).prod = ∑ c : Fin t → ι, (List.ofFn fun k => f k (c k)).prod
  := by sorry
