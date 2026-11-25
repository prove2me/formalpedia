-- Prove2me | Theorems.Thm_PI_IdeleUnitsOpenW_unitIdeles_eq
-- name    : PI.IdeleUnitsOpenW.unitIdeles_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:25.063792+00:00
-- url     : https://prove2.me/theorems/a35f86e0-6efa-44cd-af99-e1111819987e
-- title:
--   Idele Units Open W: unit Ideles eq
-- statement:
--   The Idele Units Open W construction uses the unit Ideles eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleUnitsOpen/IsOpenAdicCompletionIntegers.lean#L35-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleUnitsOpen/IsOpenAdicCompletionIntegers.lean#L35-L57

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

theorem PI.IdeleUnitsOpenW.unitIdeles_eq :
    (Formalism.L2.Host.CharEx.unitIdeles L : Set (Ideles L)) =
      (fun u : Ideles L => (u : AdeleRing (𝓞 L) L)) ⁻¹' integralAdeles L ∩
        (fun u : Ideles L => ((u⁻¹ : Ideles L) : AdeleRing (𝓞 L) L)) ⁻¹' integralAdeles L := by sorry
