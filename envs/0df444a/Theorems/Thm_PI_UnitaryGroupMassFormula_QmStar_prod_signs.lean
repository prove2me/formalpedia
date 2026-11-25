-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_prod_signs
-- name    : PI.UnitaryGroupMassFormula.QmStar.prod_signs
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:35:37.602934+00:00
-- url     : https://prove2.me/theorems/57da3cd9-9b51-5974-9e9d-a7fa0b672993
-- title:
--   Qm Star: prod signs
-- statement:
--   The Qm Star construction uses the prod signs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean#L58-L66

import Definitions.Def_Formalism_PeriodIntegrals_QmStar
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmStar

theorem PI.UnitaryGroupMassFormula.QmStar.prod_signs {n t : ℕ} (ε : Fin n → ℤˣ) (a b : Fin t → Fin n) (σ : Equiv.Perm (Fin t)) :
    (∏ k : Fin t, ((ε (a (σ k.rev)) * ε (b k.rev) : ℤˣ) : ℤ)) =
      (((∏ k, ε (a k)) * ∏ k, ε (b k) : ℤˣ) : ℤ) := by sorry
