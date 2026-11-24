-- Prove2me | Theorems.Thm_PI_KLW_sum_conj
-- name    : PI.KLW.sum_conj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:54:54.624797+00:00
-- url     : https://prove2.me/theorems/52f09589-36dd-48ac-b1f4-5785dd87a776
-- title:
--   KLW: sum conj
-- statement:
--   The KLW construction uses the sum conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/EquivariantPartsOfFiniteType.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/EquivariantPartsOfFiniteType.lean#L43-L47

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
variable {K E : Type} [Field K] [Field E] [CharZero E] [Algebra K E]

theorem PI.KLW.sum_conj (cj : E ≃ₐ[ℚ] E)
    (h : ∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') {ι : Type} [Fintype ι]
    (v w : ι → K) :
    ∑ i, algebraMap K E (v i) * cj (algebraMap K E (w i)) = algebraMap K E (hf (conjK cj h) v w) := by sorry
