-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_pointwise_sum_bound
-- name    : ReciprocityTheory.ChartRestriction.G.FD.pointwise_sum_bound
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:21:52.315852+00:00
-- url     : https://prove2.me/theorems/2b164955-84fa-4b1e-b543-9f021a7f16df
-- title:
--   FD: pointwise sum bound
-- statement:
--   The FD construction uses the pointwise sum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ShortVectorBoundOfCoefficientBounds.lean#L12-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ShortVectorBoundOfCoefficientBounds.lean#L12-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentVectorEqSmulComponent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ShortVectorBoundOfCoefficientBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.pointwise_sum_bound {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    (F : (X.Ψ → Fin 2 → Fin 2 → ℂ) → Frame X.Ψ r → ℂ) (T : (X.Ψ → Fin 2 → Fin 2 → ℂ) → ℝ)
    (w S1 : ℝ) (hS10 : 0 ≤ S1) (z0 : Frame X.Ψ r)
    (hexp : ∀ z ∈ X.dom, Summable (fun χ => ‖F χ z‖) → HasSum (fun χ => F χ z) (Q z))
    (hpt : ∀ χ, ∀ z ∈ X.dom, X.SameFlag z0 z →
      X.pnorm la (F χ) z ≤ 2 ^ (w / 2) * Real.exp (-Real.pi * T χ) * S1)
    (hsum : Summable (fun j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0} => Real.exp (-Real.pi * T j.1))) :
    ∀ z ∈ X.dom, X.SameFlag z0 z → X.pnorm la Q z ≤
      2 ^ (w / 2) * (∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, Real.exp (-Real.pi * T j.1)) * S1 := by sorry
