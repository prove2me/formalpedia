-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NC_isClosed_FixXp
-- name    : PI.LevelKSplit.W.NC.isClosed_FixXp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:39:27.58089+00:00
-- url     : https://prove2.me/theorems/49e59b59-da8a-5722-b2fe-1e7fa50bcfd3
-- title:
--   NC: is Closed Fix Xp
-- statement:
--   The NC construction uses the is Closed Fix Xp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevelSAllOfSemiNHSHeisLev.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevelSAllOfSemiNHSHeisLev.lean#L16-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_CoordinateHomeomorphism
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOfSemiNHSHeisLev
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NC
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} [FiniteDimensional F E]

theorem PI.LevelKSplit.W.NC.isClosed_FixXp {r : ℕ} (P : Frame E M r) :
    IsClosed (FixXp (Af F) σ J P : Set (HA (Af F) σ J)) := by sorry
