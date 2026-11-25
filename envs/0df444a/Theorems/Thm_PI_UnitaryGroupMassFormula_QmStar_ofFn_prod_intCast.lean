-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_ofFn_prod_intCast
-- name    : PI.UnitaryGroupMassFormula.QmStar.ofFn_prod_intCast
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:06.29221+00:00
-- url     : https://prove2.me/theorems/68871dfc-b396-556b-944b-f01a42d96ac6
-- title:
--   Qm Star: of Fn prod int Cast
-- statement:
--   The Qm Star construction uses the of Fn prod int Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean#L20-L29

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

theorem PI.UnitaryGroupMassFormula.QmStar.ofFn_prod_intCast {A : Type*} [Ring A] : ∀ {t : ℕ} (s : Fin t → ℤ) (g : Fin t → A),
    (List.ofFn fun k => (s k : A) * g k).prod = ((∏ k, s k : ℤ) : A) * (List.ofFn g).prod
  := by sorry
