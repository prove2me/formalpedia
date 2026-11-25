-- Prove2me | Theorems.Thm_P2M_PI_SlopeSteps_sum_comp_perm__6a20aaa6ea80
-- name    : P2M_PI_SlopeSteps_sum_comp_perm__6a20aaa6ea80
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:00:21.293727+00:00
-- url     : https://prove2.me/theorems/509dcc72-5460-4bfa-bb06-e61ced36ac75
-- title:
--   P2 M PI Slope Steps sum comp perm  6a20aaa6ea80: P2 M PI Slope Steps sum comp perm  6a20aaa6ea80
-- statement:
--   The P2 M PI Slope Steps sum comp perm  6a20aaa6ea80 construction uses the P2 M PI Slope Steps sum comp perm  6a20aaa6ea80 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StandardSlopeBound/NablaGram.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StandardSlopeBound/NablaGram.lean#L22-L24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_MonomialFactorizationLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_StdSlopeLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SlopeSteps
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV Matrix

theorem P2M_PI_SlopeSteps_sum_comp_perm__6a20aaa6ea80 {M : Type*} [AddCommMonoid M] {k : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (F : (Fin k → n) → M) (τ : Equiv.Perm (Fin k)) : ∑ f : Fin k → n, F (fun i => f (τ i)) = ∑ f, F f := by sorry

alias «PI».«SlopeSteps».«sum_comp_perm'» := P2M_PI_SlopeSteps_sum_comp_perm__6a20aaa6ea80
