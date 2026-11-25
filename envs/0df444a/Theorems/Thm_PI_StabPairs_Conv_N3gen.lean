-- Prove2me | Theorems.Thm_PI_StabPairs_Conv_N3gen
-- name    : PI.StabPairs.Conv.N3gen
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:40.14531+00:00
-- url     : https://prove2.me/theorems/f539057c-7f09-5d52-8363-cb372f98d3c7
-- title:
--   Conv: N3gen
-- statement:
--   The Conv construction uses the N3gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/HermBvecFvec.lean#L226-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/HermBvecFvec.lean#L226-L250

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_HermBvecFvec
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
open PI PI.StabPairs PI.StabPairs.Conv
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW

theorem PI.StabPairs.Conv.N3gen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (hi : r ≤ i.val) (x : Fin (r + 1) → ℂ) (hx : x (Fin.last r) = 0)
    (h : M *ᵥ bvec j = bvec j + Ff k r z *ᵥ x) : M i j = if i = j then 1 else 0 := by sorry
