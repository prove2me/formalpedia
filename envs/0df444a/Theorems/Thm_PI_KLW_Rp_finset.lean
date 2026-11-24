-- Prove2me | Theorems.Thm_PI_KLW_Rp_finset
-- name    : PI.KLW.Rp_finset
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:54:31.721973+00:00
-- url     : https://prove2.me/theorems/03c7361e-2458-4bf3-9b50-fe7d2697d697
-- title:
--   KLW: Rp finset
-- statement:
--   The KLW construction uses the Rp finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/EquivariantPartsOfFiniteType.lean#L61-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/EquivariantPartsOfFiniteType.lean#L61-L76

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
variable {K : Type} [Field K] [NumberField K] {p : ℕ}

theorem PI.KLW.Rp_finset {α : Type} (T : Finset α) (f : α → K) (h : ∀ z ∈ T, Rp K p (f z)) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ z ∈ T, (s : K) * f z ∈ (algebraMap (𝓞 K) K).range := by sorry
