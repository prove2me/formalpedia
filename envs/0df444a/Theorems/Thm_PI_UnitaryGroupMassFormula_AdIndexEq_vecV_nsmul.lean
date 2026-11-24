-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_vecV_nsmul
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.vecV_nsmul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:48:42.719011+00:00
-- url     : https://prove2.me/theorems/e0ee44bd-d566-4241-b9b4-2b520dadb956
-- title:
--   Ad Index Eq: vec V nsmul
-- statement:
--   The Ad Index Eq construction uses the vec V nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/Reduce.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/Reduce.lean#L44-L48

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.vecV_nsmul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (N : ℕ)
    (u : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (N • u) = N • PI.FinKW.vecV I v u := by sorry
