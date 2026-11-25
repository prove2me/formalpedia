-- Prove2me | Theorems.Thm_PI_Dv_GLP_tau_eS_comm
-- name    : PI.Dv.GLP.tau_eS_comm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:18.089604+00:00
-- url     : https://prove2.me/theorems/de8ffc2e-a881-4ac1-8cc2-5e99e245840c
-- title:
--   GLP: tau e S comm
-- statement:
--   The GLP construction uses the tau e S comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L139-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L139-L149

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

theorem PI.Dv.GLP.tau_eS_comm (T : GoodSet K G) (s t : T.S) (g : G) :
    (T.tau t).asAlgebraHom (eS T s) * T.tau t g = T.tau t g * (T.tau t).asAlgebraHom (eS T s) := by sorry
