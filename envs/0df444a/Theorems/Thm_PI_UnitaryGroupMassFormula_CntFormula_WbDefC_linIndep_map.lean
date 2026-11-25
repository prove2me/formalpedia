-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_WbDefC_linIndep_map
-- name    : PI.UnitaryGroupMassFormula.CntFormula.WbDefC.linIndep_map
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:31:32.793813+00:00
-- url     : https://prove2.me/theorems/567a12bf-5b6d-5b81-a4c8-6baf539fe91d
-- title:
--   Wb Def C: lin Indep map
-- statement:
--   The Wb Def C construction uses the lin Indep map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/CTEqConjTranspose.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/CTEqConjTranspose.lean#L81-L84

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Lemmata_MiscLemmasI_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_CTEqConjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.WbDefC

theorem PI.UnitaryGroupMassFormula.CntFormula.WbDefC.linIndep_map {K L ι n : Type} [Field K] [Field L] [Fintype ι] [Fintype n] [DecidableEq ι]
    [DecidableEq n] (τ : K →+* L) (c : ι → n → K) (hc : LinearIndependent K c) :
    LinearIndependent L (fun a => fun i => τ (c a i)) := by sorry
