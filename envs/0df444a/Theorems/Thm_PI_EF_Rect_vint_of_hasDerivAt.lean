-- Prove2me | Theorems.Thm_PI_EF_Rect_vint_of_hasDerivAt
-- name    : PI.EF.Rect.vint_of_hasDerivAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:47.651163+00:00
-- url     : https://prove2.me/theorems/e6685514-fefd-441e-93ad-3d859d93630c
-- title:
--   Rect: vint of has Deriv At
-- statement:
--   The Rect construction uses the vint of has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L39-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L39-L54

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Rect
open Complex MeasureTheory intervalIntegral Set Filter Topology Real

theorem PI.EF.Rect.vint_of_hasDerivAt {F f : ℂ → ℂ} {a b₁ b₂ : ℝ}
    (h : ∀ y ∈ uIcc b₁ b₂, HasDerivAt F (f (a + y * I)) (a + y * I))
    (hc : ∀ y ∈ uIcc b₁ b₂, ContinuousAt f (a + y * I)) :
    I • ∫ y : ℝ in b₁..b₂, f (a + y * I) = F (a + b₂ * I) - F (a + b₁ * I) := by sorry
