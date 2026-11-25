-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_locInert_of
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.locInert_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:50:24.429648+00:00
-- url     : https://prove2.me/theorems/fcb645e5-4e05-44b5-9278-67c45aa57699
-- title:
--   Ad Index Eq: loc Inert of
-- statement:
--   The Ad Index Eq construction uses the loc Inert of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/Assemble.lean#L148-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/Assemble.lean#L148-L154

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.locInert_of (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (hK : KLocGlob)
    (h : LocInertChi) : LocInert := by sorry
