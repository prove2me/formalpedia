-- Prove2me | Theorems.Thm_PI_Dv_TIW_theta_smul
-- name    : PI.Dv.TIW.theta_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:28.71983+00:00
-- url     : https://prove2.me/theorems/0dc45692-7afd-40f9-8bcb-586ab7abde1d
-- title:
--   TIW: theta smul
-- statement:
--   The TIW construction uses the theta smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TauCentralScalar.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TauCentralScalar.lean#L23-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G) (s : T.S)

theorem PI.Dv.TIW.theta_smul (c : K) (M : Module.End K (T.W s)) : theta T s (c • M) = c • theta T s M := by sorry
