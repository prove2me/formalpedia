-- Prove2me | Theorems.Thm_PI_StabPairsW_expand_of_tail
-- name    : PI.StabPairsW.expand_of_tail
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:37.243128+00:00
-- url     : https://prove2.me/theorems/28276cdf-ab25-40a8-8c65-0a89c44fb941
-- title:
--   Stab Pairs W: expand of tail
-- statement:
--   The Stab Pairs W construction uses the expand of tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/Forward.lean#L25-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/Forward.lean#L25-L83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}

theorem PI.StabPairsW.expand_of_tail (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (b : Fin (r + 1))
    (y : Fin (2 * r + k + 1) → ℂ) (hy : ∀ i : Fin (2 * r + k + 1), b.val ≤ i.val → y i = fvec k r z b i) :
    y = ∑ a, coefOf (k := k) b y a • fvec k r z a := by sorry
