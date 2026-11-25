-- Prove2me | Theorems.Thm_PI_CompDegEF_mem_integralClosure_iff_mem_ball
-- name    : PI.CompDegEF.mem_integralClosure_iff_mem_ball
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:26:31.332595+00:00
-- url     : https://prove2.me/theorems/115a49cd-08ec-4241-9fd0-c6fd19679403
-- title:
--   Comp Deg EF: mem integral Closure iff mem ball
-- statement:
--   The Comp Deg EF construction uses the mem integral Closure iff mem ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/MemIntegralClosureIffMemBall.lean#L71-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/MemIntegralClosureIffMemBall.lean#L71-L78

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_MemIntegralClosureIffMemBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
variable {l : ℕ} [hl : Fact l.Prime]

theorem PI.CompDegEF.mem_integralClosure_iff_mem_ball (K : FinExt l) (x : ↥K.1) :
    x ∈ integralClosure ℤ_[l] ↥K.1 ↔ x ∈ ball K := by sorry
