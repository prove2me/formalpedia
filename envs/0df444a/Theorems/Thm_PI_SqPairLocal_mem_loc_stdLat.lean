-- Prove2me | Theorems.Thm_PI_SqPairLocal_mem_loc_stdLat
-- name    : PI.SqPairLocal.mem_loc_stdLat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:32:52.738736+00:00
-- url     : https://prove2.me/theorems/a603334d-b3f7-40fd-ae47-59e128c645d5
-- title:
--   Sq Pair Local: mem loc std Lat
-- statement:
--   The Sq Pair Local construction uses the mem loc std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnimodularOfIsSDG.lean#L55-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnimodularOfIsSDG.lean#L55-L75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnimodGenus
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnimodularOfIsSDG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG PI.UG
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem PI.SqPairLocal.mem_loc_stdLat {Q : Ideal (𝓞 E)} (hQ : Q.IsPrime) (hc : Q.comap (cj E) = Q) {N : ℕ}
    (x : Fin N → E) : x ∈ loc (K := E) Q (stdLat E N) ↔ ∀ i, IntAt Q (x i) := by sorry
