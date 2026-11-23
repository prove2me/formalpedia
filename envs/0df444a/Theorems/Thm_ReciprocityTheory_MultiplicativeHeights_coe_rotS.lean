-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_coe_rotS
-- name    : ReciprocityTheory.MultiplicativeHeights.coe_rotS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:37.695698+00:00
-- url     : https://prove2.me/theorems/07e9b678-e91a-4aa1-a135-be3e8394ec9b
-- title:
--   Multiplicative Heights: coe rot S
-- statement:
--   The Multiplicative Heights construction uses the coe rot S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/MeasurePreservingSphereMap.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/MeasurePreservingSphereMap.lean#L88-L93

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

theorem ReciprocityTheory.MultiplicativeHeights.coe_rotS {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ)
    (z : UnitSphereC n) :
    (rotS hu θ z : EuclideanSpace ℂ (Fin n)) =
      inner ℂ u (z : EuclideanSpace ℂ (Fin n)) • u +
        circleMap 0 1 θ • ((z : EuclideanSpace ℂ (Fin n)) - inner ℂ u (z : EuclideanSpace ℂ (Fin n)) • u) := by sorry
