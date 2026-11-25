-- Prove2me | Theorems.Thm_PI_UMultOne_GelfSpanWork_repEnd_mem
-- name    : PI.UMultOne.GelfSpanWork.repEnd_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:29:28.873223+00:00
-- url     : https://prove2.me/theorems/1a6906c7-0213-41fe-aadd-eeb0baef41b6
-- title:
--   Gelf Span Work: rep End mem
-- statement:
--   The Gelf Span Work construction uses the rep End mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralSpanAlgebra/Burnside.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralSpanAlgebra/Burnside.lean#L38-L39

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

theorem PI.UMultOne.GelfSpanWork.repEnd_mem (ρ : G →* GL (Fin N) ℂ) (g : G) : repEnd ρ g ∈ spanAlg ρ := by sorry
