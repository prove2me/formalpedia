-- Prove2me | Theorems.Thm_PI_SqPairLocal_mem_loc_inert
-- name    : PI.SqPairLocal.mem_loc_inert
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:36:08.727878+00:00
-- url     : https://prove2.me/theorems/1806d57f-d392-45e6-8d4b-e3c984a5f757
-- title:
--   Sq Pair Local: mem loc inert
-- statement:
--   The Sq Pair Local construction uses the mem loc inert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnimodularOfIsSDG.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnimodularOfIsSDG.lean#L50-L53

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

theorem PI.SqPairLocal.mem_loc_inert {Q : Ideal (𝓞 E)} (hQ : Q.IsPrime) (hc : Q.comap (cj E) = Q) {N : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    y ∈ loc (K := E) Q L ↔ ∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L := by sorry
