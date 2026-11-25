-- Prove2me | Theorems.Thm_PI_KLW_Rp_fintype
-- name    : PI.KLW.Rp_fintype
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:32:54.512802+00:00
-- url     : https://prove2.me/theorems/ca91dee9-5e14-5445-a78e-5c521f765c0b
-- title:
--   KLW: Rp fintype
-- statement:
--   The KLW construction uses the Rp fintype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/EquivariantPartsOfFiniteType.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/EquivariantPartsOfFiniteType.lean#L78-L81

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

theorem PI.KLW.Rp_fintype {α : Type} [Fintype α] (f : α → K) (h : ∀ z, Rp K p (f z)) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ z, (s : K) * f z ∈ (algebraMap (𝓞 K) K).range := by sorry
