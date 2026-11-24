-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_Gl_vecV_sub
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.Gl.vecV_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:51:51.030877+00:00
-- url     : https://prove2.me/theorems/df15ad17-bb7e-4c9e-a08d-6b3eeb1a13e5
-- title:
--   Gl: vec V sub
-- statement:
--   The Gl construction uses the vec V sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/GlueHoldsVar.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/GlueHoldsVar.lean#L30-L33

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.Gl
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists PI.UnitaryGroupMassFormula.AdIndexEq

theorem PI.UnitaryGroupMassFormula.ScXuExists.Gl.vecV_sub (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x y : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (x - y) = PI.FinKW.vecV I v x - PI.FinKW.vecV I v y := by sorry
