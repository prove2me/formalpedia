-- Prove2me | Theorems.Thm_PI_Dv_IdxW_den_of_span
-- name    : PI.Dv.IdxW.den_of_span
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:36:33.339663+00:00
-- url     : https://prove2.me/theorems/619e3bff-40dd-4566-b689-f2e46a5c0731
-- title:
--   Idx W: den of span
-- statement:
--   The Idx W construction uses the den of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/IsLocalizedModuleToSpan.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/IsLocalizedModuleToSpan.lean#L151-L154

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ElementDenominator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.IdxW
open Module
variable {K : Type*} [Field K] {R : Type*} [CommRing R] [IsDomain R] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
omit [IsScalarTower R K V]

theorem PI.Dv.IdxW.den_of_span (X Y : Submodule R V) (hX : X.FG) [IsScalarTower R K V]
    (h : Submodule.span K (X : Set V) = Submodule.span K (Y : Set V)) :
    ∃ c : R, c ≠ 0 ∧ ∀ x ∈ X, c • x ∈ Y := by sorry
