-- Prove2me | Theorems.Thm_PI_IdeleUnitsOpenW_isOpen_adicCompletionIntegers
-- name    : PI.IdeleUnitsOpenW.isOpen_adicCompletionIntegers
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:10.341598+00:00
-- url     : https://prove2.me/theorems/5e5d52ea-387a-4e8d-854f-e3cfcdf97d1d
-- title:
--   Idele Units Open W: is Open adic Completion Integers
-- statement:
--   The Idele Units Open W construction uses the is Open adic Completion Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleUnitsOpen/IsOpenAdicCompletionIntegers.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleUnitsOpen/IsOpenAdicCompletionIntegers.lean#L10-L18

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharExGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleUnitsOpen_IsOpenAdicCompletionIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open PI PI.IdeleUnitsOpenW
variable (L : Type) [Field L] [NumberField L]

theorem PI.IdeleUnitsOpenW.isOpen_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 L)) :
    IsOpen (v.adicCompletionIntegers L : Set (v.adicCompletion L)) := by sorry
