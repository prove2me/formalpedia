-- Prove2me | Theorems.Thm_PI_EF_Loc_le_norm_refl
-- name    : PI.EF.Loc.le_norm_refl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:17.529349+00:00
-- url     : https://prove2.me/theorems/68625610-ff89-4d1a-b9ab-b2eabcc56b62
-- title:
--   Loc: le norm refl
-- statement:
--   The Loc construction uses the le norm refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/NormLogDerivReflLe.lean#L25-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/NormLogDerivReflLe.lean#L25-L38

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

theorem PI.EF.Loc.le_norm_refl {s₀ ρ z : ℂ} {R R' : ℝ} (hR : 0 < R) (hρ : ρ ∈ closedBall s₀ R')
    (hz : z ∈ closedBall s₀ R) : R - R' ≤ ‖refl s₀ R ρ z‖ := by sorry
