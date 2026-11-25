-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_exists_implicit_section
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.exists_implicit_section
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:30.578143+00:00
-- url     : https://prove2.me/theorems/80d0f377-4fe5-45d0-a731-a3824ecc6404
-- title:
--   Fib: exists implicit section
-- statement:
--   The Fib construction uses the exists implicit section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L339-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L339-L375

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.exists_implicit_section {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (f : E × ℂ → ℂ) (u : E × ℂ) (hf : ContDiffAt ℂ 1 f u) {c : ℂ} (hc : c ≠ 0)
    (hd : HasDerivAt (fun t => f (u.1, t)) c u.2) :
    ∃ (U : Set E) (τ : E → ℂ), IsOpen U ∧ u.1 ∈ U ∧ DifferentiableOn ℂ τ U ∧ τ u.1 = u.2 ∧
      ∀ w ∈ U, f (w, τ w) = f u := by sorry
