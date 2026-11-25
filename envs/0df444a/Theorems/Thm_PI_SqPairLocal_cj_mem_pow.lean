-- Prove2me | Theorems.Thm_PI_SqPairLocal_cj_mem_pow
-- name    : PI.SqPairLocal.cj_mem_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:24:49.322772+00:00
-- url     : https://prove2.me/theorems/14c71525-6691-59b1-8f5a-24f1582ee05f
-- title:
--   Sq Pair Local: cj mem pow
-- statement:
--   The Sq Pair Local construction uses the cj mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L107-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L107-L112

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
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
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

theorem PI.SqPairLocal.cj_mem_pow {I : Ideal (𝓞 E)} {K : ℕ} {x : 𝓞 E} (h : x ∈ (I.comap (cj E)) ^ K) :
    cj E x ∈ I ^ K := by sorry
