-- Prove2me | Theorems.Thm_PI_KLW_Ind_split_step
-- name    : PI.KLW.Ind.split_step
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:33:36.101155+00:00
-- url     : https://prove2.me/theorems/3b30c691-1400-5fe8-81be-ad7ff56e3b3b
-- title:
--   Ind: split step
-- statement:
--   The Ind construction uses the split step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/LatticeFromNormOneInduction.lean#L113-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/LatticeFromNormOneInduction.lean#L113-L176

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction
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
open PI PI.KLW PI.KLW.Ind
open PI.KLW

theorem PI.KLW.Ind.split_step {K : Type} [Field K] [NumberField K] (c : K →+* K) (p : ℕ) {ι : Type}
    [Fintype ι] [DecidableEq ι] (i0 : ι) (L : Set (ι → K)) (hL : Unimod K c p L)
    (hS : Spans K L) (he : Pi.single i0 (1 : K) ∈ L)
    (hrec : ∀ L' : Set ({i // i ≠ i0} → K), Unimod K c p L' → Spans K L' →
      ∃ u : ({i // i ≠ i0} → K) ≃ₗ[K] ({i // i ≠ i0} → K),
        IsUnitary c u ∧ ∀ v, v ∈ L' ↔ ∀ j, Rp K p (u v j)) :
    ∃ u : (ι → K) ≃ₗ[K] (ι → K), IsUnitary c u ∧ ∀ v, v ∈ L ↔ ∀ i, Rp K p (u v i) := by sorry
