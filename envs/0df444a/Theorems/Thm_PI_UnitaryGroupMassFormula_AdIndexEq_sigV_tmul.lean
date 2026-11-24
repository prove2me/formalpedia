-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_sigV_tmul
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.sigV_tmul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:13.155394+00:00
-- url     : https://prove2.me/theorems/8e2308e1-90dc-48bc-8734-e74b0def75d5
-- title:
--   Ad Index Eq: sig V tmul
-- statement:
--   The Ad Index Eq construction uses the sig V tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertQRG.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertQRG.lean#L14-L17

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertQRG
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
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

theorem PI.UnitaryGroupMassFormula.AdIndexEq.sigV_tmul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v)
    (e : I.E) : sigV I v (x ⊗ₜ e) = x ⊗ₜ star e := by sorry
