-- Prove2me | Theorems.Thm_PI_EF_norm_sub_ctr_sq
-- name    : PI.EF.norm_sub_ctr_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:55.105329+00:00
-- url     : https://prove2.me/theorems/1523c64b-ed6e-4fd1-8f47-b5b11d2909a5
-- title:
--   EF: norm sub ctr sq
-- statement:
--   The EF construction uses the norm sub ctr sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/NormSubCtrSq.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/NormSubCtrSq.lean#L13-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormSubCtrSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]

theorem PI.EF.norm_sub_ctr_sq (ρ : ℂ) (t : ℝ) : ‖ρ - ctr t‖ ^ 2 = (ρ.re - 2) ^ 2 + (ρ.im - t) ^ 2 := by sorry
