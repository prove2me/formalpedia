-- Prove2me | Theorems.Thm_PI_EF_Loc_norm_refl_sphere
-- name    : PI.EF.Loc.norm_refl_sphere
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:27:46.72488+00:00
-- url     : https://prove2.me/theorems/219e5835-6a3f-4db2-ba47-0547c4ddd6c3
-- title:
--   Loc: norm refl sphere
-- statement:
--   The Loc construction uses the norm refl sphere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/NormLogDerivReflLe.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/NormLogDerivReflLe.lean#L11-L23

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

theorem PI.EF.Loc.norm_refl_sphere {s₀ ρ z : ℂ} {R : ℝ} (hR : 0 < R) (hz : z ∈ sphere s₀ R) :
    ‖refl s₀ R ρ z‖ = ‖z - ρ‖ := by sorry
