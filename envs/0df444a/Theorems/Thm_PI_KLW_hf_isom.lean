-- Prove2me | Theorems.Thm_PI_KLW_hf_isom
-- name    : PI.KLW.hf_isom
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:25.726697+00:00
-- url     : https://prove2.me/theorems/c8384b4c-19e1-5335-8698-7e90ae3af671
-- title:
--   KLW: hf isom
-- statement:
--   The KLW construction uses the hf isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/EquivariantPartsOfFiniteType.lean#L97-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/EquivariantPartsOfFiniteType.lean#L97-L101

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
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
open PI PI.KLW
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

theorem PI.KLW.hf_isom (cj : E ≃ₐ[ℚ] E)
    (h : ∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') {n : Type} [Fintype n]
    (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) (hg : PI.KerIso.IsIsom cj g₀) (x y : Fin 4 → E) :
    hf (conjK cj h) (g₀ x) (g₀ y) = ∑ a, Algebra.trace K E (x a * cj (y a)) := by sorry
