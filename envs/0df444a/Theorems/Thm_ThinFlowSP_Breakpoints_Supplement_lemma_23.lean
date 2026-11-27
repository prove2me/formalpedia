-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_Supplement_lemma_23
-- name    : ThinFlowSP.Breakpoints.Supplement.lemma_23
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T11:46:11.694627+00:00
-- url     : https://prove2.me/theorems/2ed94ec5-ec4a-4651-af72-7ffb5067d656
-- title:
--   Lemma 23 (used in the proof of Theorem 21), p. 15 — a right-monotone g whose primitive is positive arbitrarily close to 0 is positive on some (0, ε)
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ be locally integrable and right-monotone (Definition 20), and let $G(\xi)=\int_0^\xi g(\hat\xi)\,d\hat\xi$. Suppose that
--   $$\inf\{\xi>0:\ G(\xi)>0\}=0 .$$
--   Then there is $\varepsilon>0$ such that $g>0$ almost everywhere on $(0,\varepsilon)$ and $G>0$ on $(0,\varepsilon)$.
--
--   In the proof of Theorem 21 the lemma is applied to differences of label functions, to show that the sets of active and resetting arcs are constant just after the current time.
--
--   **Formalization Note** The hypothesis is stated as: for every $\delta>0$ there is $\xi\in(0,\delta)$ with $G(\xi)>0$. $G$ is an interval integral.
--
--   Differences from the source:
--
--   - encoding: inf{ξ > 0 : G(ξ) > 0} = 0 → for every δ > 0 there is ξ ∈ (0, δ) with G(ξ) > 0; reason: for the real infimum (inf ∅ = +∞) the two are equivalent; Lean's sInf ∅ = 0 would let g ≡ 0 satisfy a literal sInf hypothesis, for which the conclusion fails
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 15, Lemma 23

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_RightMonotone

open MeasureTheory

namespace ThinFlowSP.Breakpoints.Supplement

theorem lemma_23 (g : ℝ → ℝ) (hg : LocallyIntegrable g) (hrm : RightMonotone g)
    (hG : ∀ δ > 0, ∃ ξ ∈ Set.Ioo (0 : ℝ) δ, 0 < ∫ x in (0 : ℝ)..ξ, g x) :
    ∃ ε > 0, (∀ᵐ x, x ∈ Set.Ioo (0 : ℝ) ε → 0 < g x) ∧
      ∀ ξ ∈ Set.Ioo (0 : ℝ) ε, 0 < ∫ x in (0 : ℝ)..ξ, g x := by sorry

end ThinFlowSP.Breakpoints.Supplement
