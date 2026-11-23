-- Prove2me | Theorems.Thm_PI_LocalEndW_isUniformInducing_of_val
-- name    : PI.LocalEndW.isUniformInducing_of_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:47.233256+00:00
-- url     : https://prove2.me/theorems/edd74b5c-9110-4d3d-b157-6ca292419089
-- title:
--   Local End W: is Uniform Inducing of val
-- statement:
--   The Local End W construction uses the is Uniform Inducing of val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/IsUniformInducingOfVal.lean#L8-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/IsUniformInducingOfVal.lean#L8-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IsUniformInducingOfVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Uniformity
open PI PI.LocalEndW

theorem PI.LocalEndW.isUniformInducing_of_val {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (τ : v.adicCompletion F →+* v.adicCompletion F) (hτ : ∀ x, Valued.v (τ x) = Valued.v x) :
    IsUniformInducing τ := by sorry
