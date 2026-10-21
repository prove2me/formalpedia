-- Prove2me | Theorems.Thm_SaddleSplit_Async_proposition_2_6
-- name    : SaddleSplit.Async.proposition_2_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:31.410111+00:00
-- url     : https://prove2.me/theorems/8153e015-85b9-4683-9d1b-e7860459cbcf
-- title:
--   Proposition 2.6, p. 10 — the outer-approximation iteration (2.32) converges weakly to a zero of the saddle operator
-- statement:
--   Consider the setting of Problem 1.1 and of Definitions 2.1 and 2.4, and suppose that $\operatorname{zer}\boldsymbol{\mathcal S}\neq\varnothing$. Let $\alpha=\min\{\alpha^c_i,\beta^c_k,\delta^c_k\}_{i\in I,k\in K}$, $\mathbf x_0\in\mathbf X$ and $\varepsilon\in\left]0,1\right[$, and iterate: for every $n$, pick $(\mathbf p_n,\mathbf p^*_n)\in\operatorname{gra}\mathbf M$ and $\mathbf q_n\in\mathbf X$, set $\mathbf t^*_n=\mathbf p^*_n+\mathbf C\mathbf q_n$ and
--   $$\Delta_n=\langle\mathbf x_n-\mathbf p_n\mid\mathbf t^*_n\rangle-(4\alpha)^{-1}\|\mathbf p_n-\mathbf q_n\|^2,$$
--   and put $\mathbf x_{n+1}=\mathbf x_n-(\lambda_n\Delta_n/\|\mathbf t^*_n\|^2)\,\mathbf t^*_n$ with $\lambda_n\in[\varepsilon,2-\varepsilon]$ if $\Delta_n>0$, $\mathbf x_{n+1}=\mathbf x_n$ otherwise (2.32). Then:
--
--   1. $\|\mathbf x_{n+1}-\mathbf z\|\le\|\mathbf x_n-\mathbf z\|$ for every $\mathbf z\in\operatorname{zer}\boldsymbol{\mathcal S}$ and every $n$;
--   2. $\sum_n\|\mathbf x_{n+1}-\mathbf x_n\|^2<+\infty$;
--   3. if $(\mathbf t^*_n)$ is bounded, then $\varlimsup\Delta_n\le0$;
--   4. if $\mathbf x_n-\mathbf p_n\rightharpoonup\mathbf 0$, $\mathbf p_n-\mathbf q_n\to\mathbf 0$ and $\mathbf t^*_n\to\mathbf 0$, then $(\mathbf x_n)$ converges weakly to a point of $\operatorname{zer}\boldsymbol{\mathcal S}$.
--
--   Algorithm 3.4 is an instance of this scheme, and Theorem 3.5 is proved by checking the hypotheses of item 4.
--
--   **Formalization Note** The standing hypotheses of Problem 1.1 are assumed and α is pinned by `IsLeast`. "$\varlimsup\Delta_n\le 0$" is stated as: for every $\delta>0$, eventually $\Delta_n\le\delta$ (this avoids the real `limsup`, which is a junk value for sequences unbounded below). If $\Delta_n>0$ then $\mathbf t^*_n\neq\mathbf 0$, so the division is never by zero.
-- source:
--   Bùi & Combettes, Multivariate monotone inclusions in saddle form, arXiv:2002.06135v3, p. 10, Proposition 2.6, (2.32) (proof pp. 10–11)

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting

namespace SaddleSplit.Async
open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

/-- Proposition 2.6, p. 10: properties of the outer-approximation iteration (2.32) for the
saddle form, under `zer 𝓢 ≠ ∅`, with `α = min{αᶜ_i, βᶜ_k, δᶜ_k}` and `ε ∈ ]0, 1[`. -/
theorem proposition_2_6 {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]
    (prob : Problem H G) (hprob : prob.Hyp) (hzer : (zer (saddleOp prob)).Nonempty)
    (α : ℝ) (hα : IsLeast (Set.range prob.αc ∪ Set.range prob.βc ∪ Set.range prob.δc) α)
    (ε : ℝ) (hε : ε ∈ Set.Ioo 0 1)
    (x p ps q t : ℕ → XSpace H G) (Δ lam : ℕ → ℝ)
    (hrun : IsOuterApproxRun prob α ε x p ps q t Δ lam) :
    (∀ z ∈ zer (saddleOp prob), ∀ n, ‖x (n + 1) - z‖ ≤ ‖x n - z‖) ∧
    Summable (fun n => ‖x (n + 1) - x n‖ ^ 2) ∧
    (Bornology.IsBounded (Set.range t) → ∀ δ > 0, ∀ᶠ n in atTop, Δ n ≤ δ) ∧
    (WeakTendsto (fun n => x n - p n) 0 → Tendsto (fun n => p n - q n) atTop (𝓝 0) →
      Tendsto t atTop (𝓝 0) → ∃ z ∈ zer (saddleOp prob), WeakTendsto x z) := by sorry

end SaddleSplit.Async
