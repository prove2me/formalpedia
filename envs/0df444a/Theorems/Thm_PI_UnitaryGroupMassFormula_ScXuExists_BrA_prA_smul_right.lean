-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_prA_smul_right
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.BrA.prA_smul_right
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:03:09.217705+00:00
-- url     : https://prove2.me/theorems/87061603-a040-45f3-8940-90098970d122
-- title:
--   Br A: pr A smul right
-- statement:
--   The Br A construction uses the pr A smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SecondCoordinateVectorMemSpan.lean#L161-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SecondCoordinateVectorMemSpan.lean#L161-L162

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrA
open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
variable {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (P : Matrix (Fin n) (Fin n) K)

theorem PI.UnitaryGroupMassFormula.ScXuExists.BrA.prA_smul_right (c : K) (β x : Fin n → K) : pr P β (c • x) = c * pr P β x := by sorry
