-- Prove2me | Theorems.Thm_PI_QmColExpWork_extByZero_succ
-- name    : PI.QmColExpWork.extByZero_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:30.644898+00:00
-- url     : https://prove2.me/theorems/b15306a1-01d2-4547-8040-ad3a6066b042
-- title:
--   Qm Col Exp Work: ext By Zero succ
-- statement:
--   The Qm Col Exp Work construction uses the ext By Zero succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialFirstColumn/FirstColumnSplitBijective.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialFirstColumn/FirstColumnSplitBijective.lean#L37-L38

import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialFirstColumn_FirstColumnSplitBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.QmColExpWork
open Formalism.REAL

theorem PI.QmColExpWork.extByZero_succ {m : ℕ} (τ : Equiv.Perm (Fin m)) (k : Fin m) : ext0 τ k.succ = (τ k).succ := by sorry
