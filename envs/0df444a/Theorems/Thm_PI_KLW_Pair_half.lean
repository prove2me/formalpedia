-- Prove2me | Theorems.Thm_PI_KLW_Pair_half
-- name    : PI.KLW.Pair.half
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:27:22.790208+00:00
-- url     : https://prove2.me/theorems/b0078740-37a7-4d01-899f-e953fc47d613
-- title:
--   Pair: half
-- statement:
--   The Pair construction uses the half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/PairOfEps.lean#L26-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/PairOfEps.lean#L26-L100

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairOfEps
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
open NumberField
open PI PI.KLW PI.KLW.Pair
open PI.KLW

theorem PI.KLW.Pair.half {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (hK : Module.finrank ℚ K = 2) (hne : ∃ z, c z ≠ z) {p : ℕ} (hp : p.Prime) {ι : Type}
    [Fintype ι] [Nonempty ι] {L : Set (ι → K)} (hL : Unimod K c p L) (hS : Spans K L) {ε : K}
    (hε : Rp K p ε) (hsum : ε + c ε = 1) (hδ : Rp K p (ε * c ε / (p : K) ^ 2)) :
    ∃ x ∈ L, ∃ y ∈ L, ¬ Rp K p (ε * hf c x y / p) := by sorry
