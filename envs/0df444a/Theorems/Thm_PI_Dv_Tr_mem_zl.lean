-- Prove2me | Theorems.Thm_PI_Dv_Tr_mem_zl
-- name    : PI.Dv.Tr.mem_zl
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:15.515955+00:00
-- url     : https://prove2.me/theorems/2012c1fb-5c79-4140-a83f-5441f92f6580
-- title:
--   Tr: mem zl
-- statement:
--   The Tr construction uses the mem zl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/DegGeOfInj.lean#L71-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/DegGeOfInj.lean#L71-L72

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegGeOfInj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open Formalism.HN
variable {R : Type} [Ring R] {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem PI.Dv.Tr.mem_zl {ρ : V →+ E} {L : Submodule R V} {u : E} : u ∈ zl ρ L ↔ ∃ x ∈ L, ρ x = u := by sorry
