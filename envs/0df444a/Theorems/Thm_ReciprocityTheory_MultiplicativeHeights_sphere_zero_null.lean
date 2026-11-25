-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sphere_zero_null
-- name    : ReciprocityTheory.MultiplicativeHeights.sphere_zero_null
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:04:50.318514+00:00
-- url     : https://prove2.me/theorems/10faca4e-29c4-4a64-ad9f-c1f6a7299368
-- title:
--   Multiplicative Heights: sphere zero null
-- statement:
--   The Multiplicative Heights construction uses the sphere zero null property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/IntCoresA.lean#L13-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/IntCoresA.lean#L13-L78

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresA
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

theorem ReciprocityTheory.MultiplicativeHeights.sphere_zero_null (hSJ : SJStatement) {n a : ℕ} (g : MvPolynomial (Fin n) ℂ)
    (hg : g.IsHomogeneous a) (u : EuclideanSpace ℂ (Fin n)) (hu : ‖u‖ = 1)
    (hgu : MvPolynomial.eval (WithLp.ofLp u) g ≠ 0) :
    sphereProb n {z | MvPolynomial.eval (spherePoint z) g = 0} = 0 := by sorry
