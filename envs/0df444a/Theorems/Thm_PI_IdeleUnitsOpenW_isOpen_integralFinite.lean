-- Prove2me | Theorems.Thm_PI_IdeleUnitsOpenW_isOpen_integralFinite
-- name    : PI.IdeleUnitsOpenW.isOpen_integralFinite
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:33.281034+00:00
-- url     : https://prove2.me/theorems/a2724a57-1e36-4e1a-9328-daf242738d1c
-- title:
--   Idele Units Open W: is Open integral Finite
-- statement:
--   The Idele Units Open W construction uses the is Open integral Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleUnitsOpen/IsOpenAdicCompletionIntegers.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleUnitsOpen/IsOpenAdicCompletionIntegers.lean#L20-L22

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

theorem PI.IdeleUnitsOpenW.isOpen_integralFinite :
    IsOpen {f : FiniteAdeleRing (𝓞 L) L | ∀ v, f v ∈ v.adicCompletionIntegers L} := by sorry
