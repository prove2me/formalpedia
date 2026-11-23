-- Prove2me | Theorems.Thm_PI_LocalEndW_exists_N
-- name    : PI.LocalEndW.exists_N
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:41.147614+00:00
-- url     : https://prove2.me/theorems/54148ee5-6548-4e9a-8bdd-1796fd558678
-- title:
--   Local End W: exists N
-- statement:
--   The Local End W construction uses the exists N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/IntVal.lean#L18-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/IntVal.lean#L18-L45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocalEnd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IntVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WithZero
open PI PI.LocalEndW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem PI.LocalEndW.exists_N : ∃ N : ℕ, 0 < N ∧ ∃ m : ℕ, 0 < m ∧
    Valued.v ((N : v.adicCompletion F)) = exp (-(m : ℤ)) ∧
    ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → Valued.v ((ℓ : v.adicCompletion F)) = 1 := by sorry
