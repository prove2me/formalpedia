-- Prove2me | Theorems.Thm_PI_EF_Loc_differentiable_refl
-- name    : PI.EF.Loc.differentiable_refl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:26.792957+00:00
-- url     : https://prove2.me/theorems/b7bce17b-f454-45e0-9144-bdd92c187820
-- title:
--   Loc: differentiable refl
-- statement:
--   The Loc construction uses the differentiable refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/NormLogDerivReflLe.lean#L49-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/NormLogDerivReflLe.lean#L49-L50

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormLogDerivReflLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Loc
open Complex Metric Set Filter Topology ComplexConjugate

theorem PI.EF.Loc.differentiable_refl (s₀ : ℂ) (R : ℝ) (ρ : ℂ) : Differentiable ℂ (refl s₀ R ρ) := by sorry
