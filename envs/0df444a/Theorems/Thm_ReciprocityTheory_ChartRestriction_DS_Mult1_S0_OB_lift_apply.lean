-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_lift_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.lift_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:00:33.306242+00:00
-- url     : https://prove2.me/theorems/560e6cf1-3c7e-4db7-9680-3f2baf65f4e6
-- title:
--   OB: lift apply
-- statement:
--   The OB construction uses the lift apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/JOrbBoundB.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/JOrbBoundB.lean#L50-L51

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_JOrbBoundB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.S0 ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.lift_apply (y : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1)) : liftVec k 1 r' y p =
    if hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 then y ⟨p.val - 1, by omega⟩ else 0 := by sorry
