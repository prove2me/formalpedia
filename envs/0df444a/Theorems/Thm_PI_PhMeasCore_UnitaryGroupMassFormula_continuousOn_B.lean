-- Prove2me | Theorems.Thm_PI_PhMeasCore_UnitaryGroupMassFormula_continuousOn_B
-- name    : PI.PhMeasCore.UnitaryGroupMassFormula.continuousOn_B
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:28.121801+00:00
-- url     : https://prove2.me/theorems/d587e232-bf97-5117-9241-65f487a411a8
-- title:
--   Unitary Group Mass Formula: continuous On B
-- statement:
--   The Unitary Group Mass Formula construction uses the continuous On B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmoothTranslationMeasure/Development.lean#L58-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmoothTranslationMeasure/Development.lean#L58-L92

import Definitions.Def_Formalism_PeriodIntegrals_PhMeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.PhMeasCore PI.PhMeasCore.UnitaryGroupMassFormula
open PI.PhMeasCore

theorem PI.PhMeasCore.UnitaryGroupMassFormula.continuousOn_B {n : ℕ} {Hm : Matrix (Fin n) (Fin n) ℂ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {Wp : Type} [NormedAddCommGroup Wp]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {B : H → Wp} {w : H}
    (hS : StepSub) (hW : StepWord) (hmul : MulOnUH Hm σ)
    (hexp : ∀ X, InLie Hm X → ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH Hm)
    (hadd : ∀ v ∈ smoothVecs Hm σ, ∀ v' ∈ smoothVecs Hm σ, B (v + v') = B v + B v')
    (hB : IsCWCont Hm σ B) (hw : w ∈ smoothVecs Hm σ) :
    ContinuousOn (fun g => B (σ g w)) (UH Hm) := by sorry
