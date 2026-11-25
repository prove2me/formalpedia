-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NC_ncoord_of_parts
-- name    : PI.LevelKSplit.W.NC.ncoord_of_parts
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:57:16.793509+00:00
-- url     : https://prove2.me/theorems/59215e10-3ed2-4fe8-98ff-f3c6aca6e5c7
-- title:
--   NC: ncoord of parts
-- statement:
--   The NC construction uses the ncoord of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevelSAllOfSemiNHSHeisLev.lean#L27-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevelSAllOfSemiNHSHeisLev.lean#L27-L71

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

theorem PI.LevelKSplit.W.NC.ncoord_of_parts (hH : HeisP F E σ M J) (hL : LevP F E σ M J) : NCoord F E σ M J := by sorry
