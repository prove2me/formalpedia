-- Prove2me | Theorems.Thm_PI_FoldMult_UnitaryGroupMassFormula_mult_eq_iSup
-- name    : PI.FoldMult.UnitaryGroupMassFormula.mult_eq_iSup
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:31:12.815805+00:00
-- url     : https://prove2.me/theorems/56c1df2e-0466-5849-952c-cf270d77febb
-- title:
--   Unitary Group Mass Formula: mult eq i Sup
-- statement:
--   The Unitary Group Mass Formula construction uses the mult eq i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MultiplicityMeasurability/MeasurableMult.lean#L91-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MultiplicityMeasurability/MeasurableMult.lean#L91-L116

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FoldMult
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MultiplicityMeasurability_MeasurableMult
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open PI PI.FoldMult PI.FoldMult.UnitaryGroupMassFormula
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem PI.FoldMult.UnitaryGroupMassFormula.mult_eq_iSup (Γ : Subgroup G) [DiscreteTopology Γ] (Ω : Set G) (hΩ : IsCompact Ω)
    (x : G) : Formalism.L2.SG.FoldBound.mult Γ Ω x =
      ⨆ A : Finset Γ, (hitSet Γ Ω A).indicator (fun _ => (A.card : ℝ≥0∞)) x := by sorry
