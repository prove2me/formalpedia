-- Prove2me | Theorems.Thm_PI_SqPairLocal_isMaximal_comap_cj
-- name    : PI.SqPairLocal.isMaximal_comap_cj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:24:19.524184+00:00
-- url     : https://prove2.me/theorems/50a13370-589e-4977-b163-f27622a8b14d
-- title:
--   Sq Pair Local: is Maximal comap cj
-- statement:
--   The Sq Pair Local construction uses the is Maximal comap cj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L103-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L103-L105

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

theorem PI.SqPairLocal.isMaximal_comap_cj {Q : Ideal (𝓞 E)} (hQ : Q.IsMaximal) : (Q.comap (cj E)).IsMaximal := by sorry
