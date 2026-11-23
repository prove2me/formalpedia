-- Prove2me | Theorems.Thm_SaddleSplit_Async_Supplement_lemma_A_5
-- name    : SaddleSplit.Async.Supplement.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:18:39.105816+00:00
-- url     : https://prove2.me/theorems/ac80543e-6f71-4bdc-b8a7-53b118770f29
-- title:
--   Lemma A.5, p. 32 — Haugazeau-type outer approximation (A.4): monotone distance to x₀, square-summable steps, strong convergence to proj_Z x₀
-- statement:
--   Let $\mathcal K$ be a real Hilbert space, let $Z\subset\mathcal K$ be nonempty, closed and convex, and let $x_0\in\mathcal K$. Suppose that the sequences $(x_n)$, $(t^*_n)$ in $\mathcal K$ and $(\eta_n)$, $(\Delta_n)$, $(\kappa_n)$, $(\lambda_n)$ in $\mathbb R$ satisfy, for every $n\in\mathbb N$,
--
--   1. $Z\subset H_n=\{x\in\mathcal K\mid\langle x\mid t^*_n\rangle\leqslant\eta_n\}$ and $\Delta_n=\langle x_n\mid t^*_n\rangle-\eta_n$;
--   2. if $\Delta_n>0$: with $\tau_n=\|t^*_n\|^2$, $\varsigma_n=\|x_0-x_n\|^2$, $\chi_n=\langle x_0-x_n\mid t^*_n\rangle$ and $\rho_n=\tau_n\varsigma_n-\chi_n^2$, one has $(\kappa_n,\lambda_n)=(1,\Delta_n/\tau_n)$ if $\rho_n=0$, $(\kappa_n,\lambda_n)=(0,(\Delta_n+\chi_n)/\tau_n)$ if $\rho_n\neq0$ and $\chi_n\Delta_n\geqslant\rho_n$, $(\kappa_n,\lambda_n)=(1-\chi_n\Delta_n/\rho_n,\varsigma_n\Delta_n/\rho_n)$ otherwise, and
--   $$x_{n+1}=(1-\kappa_n)x_0+\kappa_nx_n-\lambda_nt^*_n;$$
--   3. if $\Delta_n\leqslant0$: $x_{n+1}=x_n$.
--
--   Then:
--
--   1. for every $n$, $\|x_n-x_0\|\leqslant\|x_{n+1}-x_0\|\leqslant\|\operatorname{proj}_Zx_0-x_0\|$;
--   2. $\sum_n\|x_{n+1}-x_n\|^2<+\infty$ and $\sum_n\|\operatorname{proj}_{H_n}x_n-x_n\|^2<+\infty$;
--   3. if, for every $x\in\mathcal K$ and every strictly increasing sequence $(k_n)$ in $\mathbb N$, $x_{k_n}\rightharpoonup x$ implies $x\in Z$, then $x_n\to\operatorname{proj}_Zx_0$ strongly.
--
--   This is the paper's Haugazeau-type outer approximation principle: each step projects $x_0$ onto the intersection of the current half-space $H_n$ and the half-space $\{x\mid\langle x-x_n\mid x_0-x_n\rangle\leqslant0\}$. Proposition 2.7 applies it with $Z=\operatorname{zer}\boldsymbol{\mathcal S}$, and through it Theorem 3.7 obtains strong convergence.
--
--   **Formalization Note** The initial point is $x_0=x(0)$. The case split of (A.4) is written as $(\kappa_n,\lambda_n)=\Xi(\Delta_n,\tau_n,\varsigma_n,\chi_n)$ with $\Xi$ of (2.33), which has the same three branches. Summability of a nonnegative real series is `Summable`. $\operatorname{proj}_C$ is a choice-defined nearest point that returns its argument when no nearest point exists; $Z$ and every $H_n$ (which contains $Z$) are nonempty, closed and convex, so the nearest point exists and is unique and the fallback is never used. Weak convergence is the published `WeakTendsto`.
--
--   Differences from the source:
--   - encoding: proj_Z x₀ and proj_{H_n} x_n, the projections onto nonempty closed convex sets → `proj`, a choice-defined nearest point with fallback value x; reason: Z and H_n ⊇ Z are nonempty, closed and convex in a Hilbert space, so the nearest point exists and is unique and `proj` equals the paper's projection on every instance.
--   - encoding: the nested case split of (A.4) on ρ_n → `(κ n, lam n) = Xi Δ τ ς χ` with Ξ of (2.33) extended to ℝ⁴; reason: Ξ has exactly the three branches of (A.4), and it is evaluated only where Δ_n > 0 and τ_n > 0 (Δ_n > 0 forces t*_n ≠ 0, since otherwise H_n = ∅ ⊉ Z).
--   - encoding: x₀ given and κ_n, λ_n defined only when Δ_n > 0 → x₀ = x 0, and κ, lam sequences constrained only when Δ n > 0; reason: same runs, the paper leaves κ_n, λ_n undefined when Δ_n ⩽ 0 and they do not enter the iteration then.
-- source:
--   Bùi & Combettes, Multivariate monotone inclusions in saddle form, arXiv:2002.06135v3, p. 32, Lemma A.5, (A.4)

import Mathlib
import Definitions.Def_SaddleSplit_Async_Supplement_Setting

namespace SaddleSplit.Async.Supplement
open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence

/-- Lemma A.5, p. 32: for a nonempty closed convex `Z` in a real Hilbert space `𝒦` and a run of
(A.4) started at `x₀ = x 0`: (i) `‖x_n − x₀‖ ⩽ ‖x_{n+1} − x₀‖ ⩽ ‖proj_Z x₀ − x₀‖` for every `n`;
(ii) `Σ‖x_{n+1} − x_n‖² < +∞` and `Σ‖proj_{H_n} x_n − x_n‖² < +∞`; (iii) if every weak sequential
cluster point of `(x_n)` lies in `Z`, then `x_n → proj_Z x₀`. -/
theorem lemma_A_5 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Z : Set E) (hZne : Z.Nonempty) (hZcl : IsClosed Z) (hZcv : Convex ℝ Z)
    (x t : ℕ → E) (η Δ κ lam : ℕ → ℝ) (hrun : IsHaugazeauRun Z x t η Δ κ lam) :
    (∀ n, ‖x n - x 0‖ ≤ ‖x (n + 1) - x 0‖ ∧ ‖x (n + 1) - x 0‖ ≤ ‖proj Z (x 0) - x 0‖) ∧
    (Summable (fun n => ‖x (n + 1) - x n‖ ^ 2) ∧
      Summable (fun n => ‖proj (halfSpace (t n) (η n)) (x n) - x n‖ ^ 2)) ∧
    ((∀ (y : E) (k : ℕ → ℕ), StrictMono k → WeakTendsto (x ∘ k) y → y ∈ Z) →
      Tendsto x atTop (𝓝 (proj Z (x 0)))) := by sorry

end SaddleSplit.Async.Supplement
