-- Prove2me | Theorems.Thm_PI_Dv_GLP_intertw_zero
-- name    : PI.Dv.GLP.intertw_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:27:40.125805+00:00
-- url     : https://prove2.me/theorems/e09b439b-ed1d-4d93-a9a8-c08f8ec3e2eb
-- title:
--   GLP: intertw zero
-- statement:
--   The GLP construction uses the intertw zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L43-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L43-L79

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.GLP.intertw_zero (T : GoodSet K G) {s t : T.S} (hst : s ≠ t) (f : T.W s →ₗ[K] T.W t)
    (hf : ∀ g x, f (T.tau s g x) = T.tau t g (f x)) : f = 0 := by sorry
