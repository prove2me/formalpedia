-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_first_coordinate_vector_smul
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.BrA.first_coordinate_vector_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:40:52.927102+00:00
-- url     : https://prove2.me/theorems/83ed365b-e9ca-4b11-8ea5-1d605dd8178c
-- title:
--   Br A: first coordinate vector smul
-- statement:
--   The Br A construction uses the first coordinate vector smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SecondCoordinateVectorMemSpan.lean#L114-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SecondCoordinateVectorMemSpan.lean#L114-L121

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

theorem PI.UnitaryGroupMassFormula.ScXuExists.BrA.first_coordinate_vector_smul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v)
    (hp : ∀ c : KV I v, p1 (algebraMap (KV I v) (RV I v) c) = c) (c : OV I v) (X : Fin I.n → RV I v) :
    vec1 p1 (c • X) = c • vec1 p1 X := by sorry
