-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_matV_inv_mul
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.matV_inv_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:39:32.294801+00:00
-- url     : https://prove2.me/theorems/445fadb9-0a13-41db-b4d3-d34301cff6b5
-- title:
--   Ad Index Eq: mat V inv mul
-- statement:
--   The Ad Index Eq construction uses the mat V inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/Reduce.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/Reduce.lean#L91-L94

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LiftMatMapSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S

theorem PI.UnitaryGroupMassFormula.AdIndexEq.matV_inv_mul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (y x : I.Gf) :
    matV I v ((y⁻¹ * x : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) =
      (matV I v (y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)))⁻¹ * matV I v (x : GL (Fin I.n) _) := by sorry
