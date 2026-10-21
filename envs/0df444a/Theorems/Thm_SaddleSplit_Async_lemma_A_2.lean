-- Prove2me | Theorems.Thm_SaddleSplit_Async_lemma_A_2
-- name    : SaddleSplit.Async.lemma_A_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:27.14686+00:00
-- url     : https://prove2.me/theorems/c2979964-fbe2-43a3-b3d1-bb0eea2588e2
-- title:
--   Lemma A.2, p. 30 — γ⁻¹Id − A is σ-strongly monotone for α-Lipschitzian A and γ ∈ ]0, 1/(α + σ)]
-- statement:
--   Let $\mathcal K$ be a real Hilbert space, $\alpha\in[0,+\infty[$, $A:\mathcal K\to\mathcal K$ $\alpha$-Lipschitzian, $\sigma\in\left]0,+\infty\right[$ and $\gamma\in\left]0,1/(\alpha+\sigma)\right]$. Then $\gamma^{-1}\mathrm{Id}-A$ is $\sigma$-strongly monotone:
--   $$\big\langle x-y\ \big|\ (\gamma^{-1}x-Ax)-(\gamma^{-1}y-Ay)\big\rangle\ \ge\ \sigma\|x-y\|^2\qquad(\forall x,y\in\mathcal K).$$
--
--   It is applied with $A=Q_i+R_i$, $B^\ell_k$, $D^\ell_k$ and the step-size ranges of Assumption 3.1.
--
--   **Formalization Note** The paper does not define "σ-strongly monotone"; the standard notion of Bauschke–Combettes (displayed above) is used. Lipschitz continuity is written $\|Ax-Ay\|\le\alpha\|x-y\|$ with a real constant $\alpha\ge0$.
-- source:
--   Bùi & Combettes, Multivariate monotone inclusions in saddle form, arXiv:2002.06135v3, p. 30, Lemma A.2

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting

namespace SaddleSplit.Async
open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

/-- Lemma A.2, p. 30: if `A` is `α`-Lipschitzian, `σ > 0` and `γ ∈ ]0, 1/(α + σ)]`, then
`γ⁻¹ Id − A` is `σ`-strongly monotone. -/
theorem lemma_A_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (α : ℝ) (hα : 0 ≤ α) (A : E → E) (hA : ∀ x y, ‖A x - A y‖ ≤ α * ‖x - y‖)
    (σ : ℝ) (hσ : 0 < σ) (γ : ℝ) (hγ : γ ∈ Set.Ioc 0 (1 / (α + σ))) :
    IsStronglyMonotone σ (fun x => γ⁻¹ • x - A x) := by sorry

end SaddleSplit.Async
