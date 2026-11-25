-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_path_bound__90ceb03416ea
-- name    : P2M_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_path_bound__90ceb03416ea
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:57:36.027841+00:00
-- url     : https://prove2.me/theorems/ca9132b9-9ce8-42e1-9bc3-d478451476ea
-- title:
--   P2 M Formalism Invariant Factor Paths Gelfand Tsetlin Bases A3comb path bound  90ceb03416ea: P2 M Formalism Invariant Factor Paths Gelfand Tsetlin Bases A3comb path bound  90ceb03416ea
-- statement:
--   The P2 M Formalism Invariant Factor Paths Gelfand Tsetlin Bases A3comb path bound  90ceb03416ea construction uses the P2 M Formalism Invariant Factor Paths Gelfand Tsetlin Bases A3comb path bound  90ceb03416ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IndexWeightsDominance.lean#L675-L683
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IndexWeightsDominance.lean#L675-L683

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb

theorem P2M_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_path_bound__90ceb03416ea {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) (i : ℕ) (hi : i ≤ N) (m : Fin n) :
    |μ i m| ≤ ((∑ k ∈ range N, B k : ℕ) : ℤ) := by sorry

alias «Formalism».«InvariantFactorPaths».«GelfandTsetlinBases».«A3comb».«path_bound'» := P2M_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_path_bound__90ceb03416ea
