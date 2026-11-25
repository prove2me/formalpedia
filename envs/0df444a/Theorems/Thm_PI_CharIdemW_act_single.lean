-- Prove2me | Theorems.Thm_PI_CharIdemW_act_single
-- name    : PI.CharIdemW.act_single
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:54.347888+00:00
-- url     : https://prove2.me/theorems/b3f94a47-ba35-5d2c-b097-4d60aa8d5afd
-- title:
--   Char Idem W: act single
-- statement:
--   The Char Idem W construction uses the act single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/Scalar.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/Scalar.lean#L15-L17

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

theorem PI.CharIdemW.act_single (W : FDRep ℂ G) (g : G) (c : ℂ) :
    act W (MonoidAlgebra.single g c) = c • W.ρ g := by sorry
