-- Prove2me | Theorems.Thm_PI_FJMX_prod_castLE_eq
-- name    : PI.FJMX.prod_castLE_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:30:22.624892+00:00
-- url     : https://prove2.me/theorems/b627f849-ca1d-4b6b-9c19-4b88552c944d
-- title:
--   FJMX: prod cast LE eq
-- statement:
--   The FJMX construction uses the prod cast LE eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L164-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L164-L182

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMX
variable {σ : Type*} {m : ℕ}

theorem PI.FJMX.prod_castLE_eq {M : Type*} [CommMonoid M] {t : ℕ} (h : t ≤ m) (g : Fin m → M) :
    ∏ i : Fin t, g (Fin.castLE h i) = ∏ i : Fin m, g i ^ (if i.val < t then 1 else 0) := by sorry
