-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_sign_conjRev
-- name    : PI.UnitaryGroupMassFormula.QmStar.sign_conjRev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:33.095209+00:00
-- url     : https://prove2.me/theorems/62c12d94-1656-42bc-95b2-72de52638e72
-- title:
--   Qm Star: sign conj Rev
-- statement:
--   The Qm Star construction uses the sign conj Rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean#L53-L56

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

theorem PI.UnitaryGroupMassFormula.QmStar.sign_conjRev {t : ℕ} (σ : Equiv.Perm (Fin t)) :
    Equiv.Perm.sign (conjRev t σ) = Equiv.Perm.sign σ := by sorry
