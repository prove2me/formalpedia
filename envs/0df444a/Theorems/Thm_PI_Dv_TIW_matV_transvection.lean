-- Prove2me | Theorems.Thm_PI_Dv_TIW_matV_transvection
-- name    : PI.Dv.TIW.matV_transvection
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:23.964402+00:00
-- url     : https://prove2.me/theorems/71db9baf-8e45-49e3-bfa9-c93774f445da
-- title:
--   TIW: mat V transvection
-- statement:
--   The TIW construction uses the mat V transvection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean#L69-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean#L69-L77

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
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
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.TIW.matV_transvection {n : Type} [Fintype n] [DecidableEq n] (i j : n) (c : K) (x : n → V) :
    matV (Matrix.transvection i j c) x = x + Pi.single i (c • x j) := by sorry
