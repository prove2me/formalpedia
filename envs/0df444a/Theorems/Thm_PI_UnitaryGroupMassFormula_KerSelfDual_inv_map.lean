-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_KerSelfDual_inv_map
-- name    : PI.UnitaryGroupMassFormula.KerSelfDual.inv_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:39:39.95686+00:00
-- url     : https://prove2.me/theorems/1fe6a9fa-78ae-465b-b72a-8f4f9e4f16fe
-- title:
--   Ker Self Dual: inv map
-- statement:
--   The Ker Self Dual construction uses the inv map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualDifferent/Imports.lean#L23-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualDifferent/Imports.lean#L23-L53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualOfDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualDifferent_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.KerSelfDual

theorem PI.UnitaryGroupMassFormula.KerSelfDual.inv_map {E : Type} [Field E] [NumberField E] (cj : E ≃ₐ[ℚ] E) (hinv : ∀ x, cj (cj x) = x)
    (𝔟 𝔟c : Ideal (𝓞 E)) (hc : ∀ x : 𝓞 E, x ∈ 𝔟c ↔ ∃ y ∈ 𝔟, cj (y : E) = (x : E))
    (hb : 𝔟 ≠ ⊥) (hbc : 𝔟c ≠ ⊥) (y : E) :
    y ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ ↔
      cj y ∈ ((𝔟c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ := by sorry
