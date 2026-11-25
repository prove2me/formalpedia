-- Prove2me | Theorems.Thm_PI_CharIdemW_trace_act_charIdem
-- name    : PI.CharIdemW.trace_act_charIdem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:57.00615+00:00
-- url     : https://prove2.me/theorems/c2b02cbd-cb88-482d-aae5-d1ce9d184764
-- title:
--   Char Idem W: trace act char Idem
-- statement:
--   The Char Idem W construction uses the trace act char Idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/Scalar.lean#L79-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/Scalar.lean#L79-L93

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open PI PI.CharIdemW
open PI.CharIdem
variable {G : Type} [Group G] [Fintype G]
open scoped Classical

theorem PI.CharIdemW.trace_act_charIdem (V W : FDRep ℂ G) [Simple V] [Simple W] :
    LinearMap.trace ℂ W (act W (charIdem V)) =
      (Module.finrank ℂ V : ℂ) * (if Nonempty (W ≅ V) then (1 : ℂ) else 0) := by sorry
