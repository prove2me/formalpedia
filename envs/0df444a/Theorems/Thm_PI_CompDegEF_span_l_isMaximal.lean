-- Prove2me | Theorems.Thm_PI_CompDegEF_span_l_isMaximal
-- name    : PI.CompDegEF.span_l_isMaximal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:30:31.634467+00:00
-- url     : https://prove2.me/theorems/98bc11fc-456c-44b9-ad9e-036718e239c5
-- title:
--   Comp Deg EF: span l is Maximal
-- statement:
--   The Comp Deg EF construction uses the span l is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/SpanLIsMaximal.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/SpanLIsMaximal.lean#L9-L13

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_SpanLIsMaximal
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

theorem PI.CompDegEF.span_l_isMaximal (l : ℕ) [hl : Fact l.Prime] : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal := by sorry
