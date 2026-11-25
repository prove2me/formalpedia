-- Prove2me | Theorems.Thm_PI_KLW_Ind_latIso_card
-- name    : PI.KLW.Ind.latIso_card
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:33:07.087805+00:00
-- url     : https://prove2.me/theorems/f8fca66a-da81-4035-a6ef-af787e68e41e
-- title:
--   Ind: lat Iso card
-- statement:
--   The Ind construction uses the lat Iso card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/LatticeFromNormOneInduction.lean#L183-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/LatticeFromNormOneInduction.lean#L183-L224

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

theorem PI.KLW.Ind.latIso_card (hN : NormOne) {K : Type} [Field K] [NumberField K] (c : K →+* K) (p : ℕ)
    (hK : Module.finrank ℚ K = 2) (hc : ∀ x, c (c x) = x) (hp : p.Prime) (hs : SplitK c p) :
    ∀ (k : ℕ) (ι : Type) [Fintype ι], Fintype.card ι = k → ∀ L : Set (ι → K),
      Unimod K c p L → Spans K L →
        ∃ u : (ι → K) ≃ₗ[K] (ι → K), IsUnitary c u ∧ ∀ v, v ∈ L ↔ ∀ i, Rp K p (u v i) := by sorry
