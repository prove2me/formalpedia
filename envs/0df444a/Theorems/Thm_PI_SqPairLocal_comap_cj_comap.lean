-- Prove2me | Theorems.Thm_PI_SqPairLocal_comap_cj_comap
-- name    : PI.SqPairLocal.comap_cj_comap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:31:34.878297+00:00
-- url     : https://prove2.me/theorems/10145d2c-4a9f-4224-9fe8-0bec23ab54e1
-- title:
--   Sq Pair Local: comap cj comap
-- statement:
--   The Sq Pair Local construction uses the comap cj comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L99-L101

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

theorem PI.SqPairLocal.comap_cj_comap (I : Ideal (𝓞 E)) : (I.comap (cj E)).comap (cj E) = I := by sorry
