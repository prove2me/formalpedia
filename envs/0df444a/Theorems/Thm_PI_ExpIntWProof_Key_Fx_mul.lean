-- Prove2me | Theorems.Thm_PI_ExpIntWProof_Key_Fx_mul
-- name    : PI.ExpIntWProof.Key.Fx.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:25.825095+00:00
-- url     : https://prove2.me/theorems/32128cd3-5ceb-4a8a-91de-11cd54feffc0
-- title:
--   Fx: mul
-- statement:
--   The Fx construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L38-L40

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof PI.ExpIntWProof.Key
variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]

theorem PI.ExpIntWProof.Key.Fx.mul {a b : R} (ha : Fx p a) (hb : Fx p b) : Fx p (a * b) := by sorry
