-- Prove2me | Theorems.Thm_PI_CompDegEF_locDegOf_of
-- name    : PI.CompDegEF.locDegOf_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:27:04.275936+00:00
-- url     : https://prove2.me/theorems/25ba1460-30e1-4a57-94a7-76fdaaf11080
-- title:
--   Comp Deg EF: loc Deg Of of
-- statement:
--   The Comp Deg EF construction uses the loc Deg Of of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/MemSpanLIff.lean#L40-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/MemSpanLIff.lean#L40-L71

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_MemSpanLIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem PI.CompDegEF.locDegOf_of (hB : BallCard) (hD : DenseSurj) (hK : KerProp) (hN : NormCard) :
    LocDegOf := by sorry
