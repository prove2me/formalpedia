-- Prove2me | Theorems.Thm_PI_SqPairLocal_powLoc_fin
-- name    : PI.SqPairLocal.powLoc_fin
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:12.340805+00:00
-- url     : https://prove2.me/theorems/304b21ce-b3e8-4f7e-8625-18b56e4bf42f
-- title:
--   Sq Pair Local: pow Loc fin
-- statement:
--   The Sq Pair Local construction uses the pow Loc fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L121-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L121-L127

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

theorem PI.SqPairLocal.powLoc_fin (hP : PowLoc) (S : Finset (Ideal (𝓞 E))) (hS : ∀ P ∈ S, P.IsMaximal)
    {c : 𝓞 E} (hc : c ≠ 0) : ∃ K : ℕ, ∀ P ∈ S, ∀ x ∈ P ^ K, Dv P c x := by sorry
