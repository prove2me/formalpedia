-- Prove2me | Theorems.Thm_PI_SqPairLocal_stdHG_conj
-- name    : PI.SqPairLocal.stdHG_conj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:26:01.026284+00:00
-- url     : https://prove2.me/theorems/50fb21bf-6e87-4a48-9f3e-e4415e962dcb
-- title:
--   Sq Pair Local: std HG conj
-- statement:
--   The Sq Pair Local construction uses the std HG conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L62-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L62-L71

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
variable {L : Submodule (𝓞 E) (Fin N → E)}

theorem PI.SqPairLocal.stdHG_conj (e : Matrix (Fin N) (Fin N) E) (x y : Fin N → E) :
    stdHG E N x (eᴴ *ᵥ y) = stdHG E N (e *ᵥ x) y := by sorry
