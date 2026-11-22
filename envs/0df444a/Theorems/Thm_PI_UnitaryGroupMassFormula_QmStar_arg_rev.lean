-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_arg_rev
-- name    : PI.UnitaryGroupMassFormula.QmStar.arg_rev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:49.628897+00:00
-- url     : https://prove2.me/theorems/a020b03b-f769-4482-97dc-eca564eeb73d
-- title:
--   Qm Star: arg rev
-- statement:
--   The Qm Star construction uses the arg rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean#L68-L75

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

theorem PI.UnitaryGroupMassFormula.QmStar.arg_rev {t : ℕ} (w : ℂ) (j : Fin t) :
    star (w - (((Fin.rev j : Fin t) : ℕ) : ℂ)) = star w - (t : ℂ) + 1 + ((j : ℕ) : ℂ) := by sorry
