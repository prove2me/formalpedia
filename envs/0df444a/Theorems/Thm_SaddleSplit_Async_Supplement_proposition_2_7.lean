-- Prove2me | Theorems.Thm_SaddleSplit_Async_Supplement_proposition_2_7
-- name    : SaddleSplit.Async.Supplement.proposition_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:19:17.531452+00:00
-- url     : https://prove2.me/theorems/9b8e6d86-7bc3-43b8-b8e8-948ab75966f0
-- title:
--   Proposition 2.7, p. 11 — the outer approximation (2.34) of zer 𝓢 converges strongly to proj_{zer 𝓢} x₀
-- statement:
--   Consider the setting of Problem 1.1: finite families of real Hilbert spaces $(\mathcal H_i)_{i\in I}$ and $(\mathcal G_k)_{k\in K}$, and operators satisfying the standing hypotheses [a]–[e]. Let $\mathbf X=\mathcal H\oplus\mathcal G\oplus\mathcal G\oplus\mathcal G$, let $\boldsymbol{\mathcal S}$ be the saddle operator of Definition 2.1, and let $\mathbf M$ and $\mathbf C$ be the operators (2.28)–(2.29) of Definition 2.4, so that $\boldsymbol{\mathcal S}=\mathbf M+\mathbf C$. Suppose that $\operatorname{zer}\boldsymbol{\mathcal S}\neq\varnothing$, set $\alpha=\min\{\alpha^c_i,\beta^c_k,\delta^c_k\}_{i\in I,k\in K}$, let $\Xi$ be the function (2.33), and let $\mathbf x_0\in\mathbf X$. Iterate, for $n=0,1,\dots$:
--
--   1. $(\mathbf p_n,\mathbf p^*_n)\in\operatorname{gra}\mathbf M$, $\mathbf q_n\in\mathbf X$, $\mathbf t^*_n=\mathbf p^*_n+\mathbf C\mathbf q_n$;
--   2. $\Delta_n=\langle\mathbf x_n-\mathbf p_n\mid\mathbf t^*_n\rangle-(4\alpha)^{-1}\|\mathbf p_n-\mathbf q_n\|^2$;
--   3. if $\Delta_n>0$: $(\kappa_n,\lambda_n)=\Xi\big(\Delta_n,\|\mathbf t^*_n\|^2,\|\mathbf x_0-\mathbf x_n\|^2,\langle\mathbf x_0-\mathbf x_n\mid\mathbf t^*_n\rangle\big)$ and $\mathbf x_{n+1}=(1-\kappa_n)\mathbf x_0+\kappa_n\mathbf x_n-\lambda_n\mathbf t^*_n$; otherwise $\mathbf x_{n+1}=\mathbf x_n$.
--
--   Then:
--
--   1. for every $n$, $\|\mathbf x_n-\mathbf x_0\|\leqslant\|\mathbf x_{n+1}-\mathbf x_0\|\leqslant\|\operatorname{proj}_{\operatorname{zer}\boldsymbol{\mathcal S}}\mathbf x_0-\mathbf x_0\|$;
--   2. $\sum_n\|\mathbf x_{n+1}-\mathbf x_n\|^2<+\infty$;
--   3. if $(\mathbf t^*_n)$ is bounded, then $\varlimsup\Delta_n\leqslant0$;
--   4. if $\mathbf x_n-\mathbf p_n\rightharpoonup\mathbf 0$, $\mathbf p_n-\mathbf q_n\to\mathbf 0$ and $\mathbf t^*_n\to\mathbf 0$, then
--   $$\mathbf x_n\to\operatorname{proj}_{\operatorname{zer}\boldsymbol{\mathcal S}}\mathbf x_0\quad\text{strongly}.$$
--
--   This is the strongly convergent counterpart of Proposition 2.6: the relaxed projection onto a half-space is replaced by a Haugazeau step anchored at $\mathbf x_0$, which makes the limit the specific zero of $\boldsymbol{\mathcal S}$ nearest to $\mathbf x_0$. Theorem 3.7 rests on it as Theorem 3.5 rests on Proposition 2.6.
--
--   **Formalization Note** $\mathbf X$ is the ℓ²-direct sum (nested `WithLp 2`), and $\boldsymbol{\mathcal S}$, $\mathbf M$, $\mathbf C$, $\operatorname{zer}$ and weak convergence are the published definitions. $\alpha$ is pinned as the least element of $\{\alpha^c_i\}\cup\{\beta^c_k\}\cup\{\delta^c_k\}$. $\varlimsup\Delta_n\leqslant0$ is written: for every $\delta>0$, eventually $\Delta_n\leqslant\delta$. Boundedness of $(\mathbf t^*_n)$ is boundedness of its range. $\operatorname{proj}$ is a choice-defined nearest point; $\operatorname{zer}\boldsymbol{\mathcal S}$ is nonempty by hypothesis and closed and convex (Proposition 2.2(ii)), so it is the true projection.
--
--   Differences from the source:
--   - encoding: proj_{zer 𝓢} x₀ → `proj`, a choice-defined nearest point with fallback value x₀; reason: zer 𝓢 is nonempty, closed and convex (Proposition 2.2(ii)) in a Hilbert space, so the nearest point exists and is unique.
--   - encoding: Ξ: ]0,+∞[ × ]0,+∞[ × ℝ × ℝ → ℝ² → `Xi` with the same three branches on ℝ⁴; reason: it is evaluated only where Δ_n > 0, and then τ_n = ‖t*_n‖² > 0 because t*_n = 0 would give Δ_n = −(4α)⁻¹‖p_n − q_n‖² ⩽ 0.
--   - encoding: lim sup Δ_n ⩽ 0 → ∀ δ > 0, eventually Δ n ≤ δ; reason: equivalent for real sequences, including those unbounded below.
--   - encoding: 𝐱₀ given and κ_n, λ_n defined only when Δ_n > 0 → 𝐱₀ = x 0, and κ, lam sequences constrained only when Δ n > 0; reason: same runs.
-- source:
--   Bùi & Combettes, Multivariate monotone inclusions in saddle form, arXiv:2002.06135v3, p. 11, Proposition 2.7, (2.33), (2.34)

import Mathlib
import Definitions.Def_SaddleSplit_Async_Supplement_Setting

namespace SaddleSplit.Async.Supplement
open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

/-- Proposition 2.7, p. 11: under `zer 𝓢 ≠ ∅`, with `α = min{αᶜ_i, βᶜ_k, δᶜ_k}`, every run of the
iteration (2.34) started at `𝐱₀ = x 0` satisfies (i) `‖x_n − x₀‖ ⩽ ‖x_{n+1} − x₀‖ ⩽
‖proj_{zer 𝓢} x₀ − x₀‖`; (ii) `Σ‖x_{n+1} − x_n‖² < +∞`; (iii) if `(t*_n)` is bounded then
`limsup Δ_n ⩽ 0`; (iv) if `x_n − p_n ⇀ 0`, `p_n − q_n → 0` and `t*_n → 0` then
`x_n → proj_{zer 𝓢} x₀`. -/
theorem proposition_2_7 {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]
    (prob : Problem H G) (hprob : prob.Hyp) (hzer : (zer (saddleOp prob)).Nonempty)
    (α : ℝ) (hα : IsLeast (Set.range prob.αc ∪ Set.range prob.βc ∪ Set.range prob.δc) α)
    (x p ps q t : ℕ → XSpace H G) (Δ κ lam : ℕ → ℝ)
    (hrun : IsStrongOuterApproxRun prob α x p ps q t Δ κ lam) :
    (∀ n, ‖x n - x 0‖ ≤ ‖x (n + 1) - x 0‖ ∧
      ‖x (n + 1) - x 0‖ ≤ ‖proj (zer (saddleOp prob)) (x 0) - x 0‖) ∧
    Summable (fun n => ‖x (n + 1) - x n‖ ^ 2) ∧
    (Bornology.IsBounded (Set.range t) → ∀ δ > 0, ∀ᶠ n in atTop, Δ n ≤ δ) ∧
    (WeakTendsto (fun n => x n - p n) 0 → Tendsto (fun n => p n - q n) atTop (𝓝 0) →
      Tendsto t atTop (𝓝 0) → Tendsto x atTop (𝓝 (proj (zer (saddleOp prob)) (x 0)))) := by
  sorry

end SaddleSplit.Async.Supplement
