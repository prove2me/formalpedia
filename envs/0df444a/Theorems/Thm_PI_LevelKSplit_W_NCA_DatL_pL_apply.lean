-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCA_DatL_pL_apply
-- name    : PI.LevelKSplit.W.NCA.DatL.pL_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:29:24.666483+00:00
-- url     : https://prove2.me/theorems/cc045627-45fd-41f5-a377-6a6eab47bb27
-- title:
--   Dat L: p L apply
-- statement:
--   The Dat L construction uses the p L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/NCAsmV.lean#L149-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/NCAsmV.lean#L149-L149

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCAsmV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA
open scoped TensorProduct
open PI.LevelKSplit.W.NCA.DatL
open PI.LevelKSplit.W.SemiG PI.LevelKSplit.W.SemiG.Dat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
  {D : PI.LevelKSplit.W.SemiG.Dat A n r}

theorem PI.LevelKSplit.W.NCA.DatL.pL_apply (v : n → A) : pL D v = v - D.pX v - D.pXv v := by sorry
