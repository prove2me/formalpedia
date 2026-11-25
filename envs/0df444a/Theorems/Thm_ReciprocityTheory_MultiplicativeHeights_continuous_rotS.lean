-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_continuous_rotS
-- name    : ReciprocityTheory.MultiplicativeHeights.continuous_rotS
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:57.644572+00:00
-- url     : https://prove2.me/theorems/4de873fd-75c9-465e-80d4-ed7262a3be74
-- title:
--   Multiplicative Heights: continuous rot S
-- statement:
--   The Multiplicative Heights construction uses the continuous rot S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/MeasurePreservingSphereMap.lean#L99-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/MeasurePreservingSphereMap.lean#L99-L109

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_MeasurePreservingSphereMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
open scoped Pointwise

theorem ReciprocityTheory.MultiplicativeHeights.continuous_rotS {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) :
    Continuous (fun p : ℝ × UnitSphereC n => rotS hu p.1 p.2) := by sorry
