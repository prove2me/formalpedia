-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_of_supp
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.modQ_of_supp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:00:24.062591+00:00
-- url     : https://prove2.me/theorems/111364e6-8289-58cf-966e-f6a4762be015
-- title:
--   Ad Index Eq: mod Q of supp
-- statement:
--   The Ad Index Eq construction uses the mod Q of supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/Assemble.lean#L141-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/Assemble.lean#L141-L144

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Assemble
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
variable (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))

theorem PI.UnitaryGroupMassFormula.AdIndexEq.modQ_of_supp (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (y : I.Gf) (hy : SuppAt I v y) :
    modQ (PI.AdIndexEq.Ksub I) y = chiV I v hC hL hJ ⟨_, hU I v y⟩ := by sorry
