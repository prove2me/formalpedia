-- Prove2me | Theorems.Thm_PI_SqPairLocal_isUnimodular_of_isSDG
-- name    : PI.SqPairLocal.isUnimodular_of_isSDG
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:35:32.92982+00:00
-- url     : https://prove2.me/theorems/45c6ef8a-81f4-5764-8d7d-52811ead3034
-- title:
--   Sq Pair Local: is Unimodular of is SDG
-- statement:
--   The Sq Pair Local construction uses the is Unimodular of is SDG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnimodularOfIsSDG.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnimodularOfIsSDG.lean#L22-L29

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

theorem PI.SqPairLocal.isUnimodular_of_isSDG {N : ℕ} {L : Submodule (𝓞 E) (Fin N → E)} (h : IsSDG E N L) :
    IsUnimodular (hStd E N) L := by sorry
