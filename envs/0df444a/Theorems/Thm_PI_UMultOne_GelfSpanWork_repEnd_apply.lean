-- Prove2me | Theorems.Thm_PI_UMultOne_GelfSpanWork_repEnd_apply
-- name    : PI.UMultOne.GelfSpanWork.repEnd_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:29:32.914928+00:00
-- url     : https://prove2.me/theorems/1442c278-e9a7-4c70-ab76-920bcfe183ac
-- title:
--   Gelf Span Work: rep End apply
-- statement:
--   The Gelf Span Work construction uses the rep End apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralSpanAlgebra/Burnside.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralSpanAlgebra/Burnside.lean#L19-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegralSpanAlgebra_Burnside
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UMultOne PI.UMultOne.GelfSpanWork
open Matrix Module
variable {G : Type} [Group G] {N : ℕ}

theorem PI.UMultOne.GelfSpanWork.repEnd_apply (ρ : G →* GL (Fin N) ℂ) (g : G) (v : Fin N → ℂ) :
    repEnd ρ g v = ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).mulVec v := by sorry
