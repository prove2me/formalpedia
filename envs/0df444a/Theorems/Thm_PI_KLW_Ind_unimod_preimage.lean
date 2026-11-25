-- Prove2me | Theorems.Thm_PI_KLW_Ind_unimod_preimage
-- name    : PI.KLW.Ind.unimod_preimage
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:33:55.683537+00:00
-- url     : https://prove2.me/theorems/8919bbd0-bdbc-506b-8afd-c2526435a9b0
-- title:
--   Ind: unimod preimage
-- statement:
--   The Ind construction uses the unimod preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/LatticeFromNormOneInduction.lean#L44-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/LatticeFromNormOneInduction.lean#L44-L57

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

theorem PI.KLW.Ind.unimod_preimage {K : Type} [Field K] [NumberField K] (c : K →+* K) (p : ℕ) {ι : Type}
    [Fintype ι] {σ : (ι → K) ≃ₗ[K] (ι → K)} (hσ : IsUnitary c σ) {L : Set (ι → K)}
    (hL : Unimod K c p L) : Unimod K c p (σ ⁻¹' L) := by sorry
