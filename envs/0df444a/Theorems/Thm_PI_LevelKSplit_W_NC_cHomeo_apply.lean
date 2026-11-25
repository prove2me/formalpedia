-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NC_cHomeo_apply
-- name    : PI.LevelKSplit.W.NC.cHomeo_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:48.016814+00:00
-- url     : https://prove2.me/theorems/eeb3c2c3-d881-4ee9-87a8-945d98e2683a
-- title:
--   NC: c Homeo apply
-- statement:
--   The NC construction uses the c Homeo apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/CoordinateHomeomorphism.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/CoordinateHomeomorphism.lean#L102-L103

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCIface
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_CoordinateHomeomorphism
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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Q : Type} [AddCommGroup Q] [TopologicalSpace Q] [ContinuousAdd Q]
variable {N A N1 Z : Subgroup G} {Lev : G → G} {sH : Q → G} {yQ : N1 → Q}

theorem PI.LevelKSplit.W.NC.cHomeo_apply (H : CoordHyp N A N1 Z Lev sH yQ) (p : A × (Q × Z)) :
    ((cHomeo H p : N) : G) = (p.1 : G) * sH p.2.1 * (p.2.2 : G) := by sorry
