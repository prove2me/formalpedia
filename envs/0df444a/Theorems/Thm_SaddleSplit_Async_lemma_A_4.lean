-- Prove2me | Theorems.Thm_SaddleSplit_Async_lemma_A_4
-- name    : SaddleSplit.Async.lemma_A_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:39.613913+00:00
-- url     : https://prove2.me/theorems/3677479d-7d7e-4f0a-9be3-a1ff4929cde6
-- title:
--   Lemma A.4, p. 31 — relaxed outer approximation onto half-spaces is Fejér monotone and converges weakly
-- statement:
--   Let $\mathcal K$ be a real Hilbert space, $Z\subset\mathcal K$ nonempty, closed and convex, $x_0\in\mathcal K$ and $\varepsilon\in\left]0,1\right[$. Suppose that for every $n$, $t^*_n\in\mathcal K$ and $\eta_n\in\mathbb R$ satisfy $Z\subset H_n=\{x\mid\langle x\mid t^*_n\rangle\le\eta_n\}$, that $\Delta_n=\langle x_n\mid t^*_n\rangle-\eta_n$, and that
--   $$x_{n+1}=\begin{cases}x_n-\dfrac{\lambda_n\Delta_n}{\|t^*_n\|^2}\,t^*_n,\ \ \lambda_n\in[\varepsilon,2-\varepsilon], & \Delta_n>0,\\[4pt] x_n, & \Delta_n\le 0.\end{cases}\qquad(A.3)$$
--   Then:
--
--   1. $\|x_{n+1}-z\|\le\|x_n-z\|$ for every $z\in Z$ and every $n$;
--   2. $\sum_n\|x_{n+1}-x_n\|^2<+\infty$;
--   3. if every weak sequential cluster point of $(x_n)$ lies in $Z$ (for every $x$ and every strictly increasing $(k_n)$, $x_{k_n}\rightharpoonup x\Rightarrow x\in Z$), then $(x_n)$ converges weakly to a point of $Z$.
--
--   This is the abstract convergence principle behind Proposition 2.6 and Algorithm 3.4.
--
--   **Formalization Note** A run is a predicate on given sequences $x,t^*,\eta,\Delta,\lambda$; $\lambda_n$ is constrained only when $\Delta_n>0$, as printed. When $\Delta_n>0$, $t^*_n\neq0$ (otherwise $Z\subset H_n$ with $Z\ne\varnothing$ forces $\eta_n\ge0$), so the division is never by zero. Weak convergence is `WeakTendsto`.
-- source:
--   Bùi & Combettes, Multivariate monotone inclusions in saddle form, arXiv:2002.06135v3, p. 31, Lemma A.4 (cited from [22], P. L. Combettes, Fejér-monotonicity in convex optimization, Encyclopedia of Optimization, 2001)

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting

namespace SaddleSplit.Async
open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

/-- Lemma A.4 ([22]), p. 31: the relaxed outer-approximation iteration (A.3) onto half-spaces
`H_n ⊃ Z` is Fejér monotone with respect to `Z`, has square-summable increments, and converges
weakly to a point of `Z` when every weak sequential cluster point lies in `Z`. -/
theorem lemma_A_4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Z : Set E) (hZne : Z.Nonempty) (hZcl : IsClosed Z) (hZcv : Convex ℝ Z)
    (ε : ℝ) (hε : ε ∈ Set.Ioo 0 1)
    (x t : ℕ → E) (η Δ lam : ℕ → ℝ) (hrun : IsFejerHalfspaceRun Z ε x t η Δ lam) :
    (∀ z ∈ Z, ∀ n, ‖x (n + 1) - z‖ ≤ ‖x n - z‖) ∧
    Summable (fun n => ‖x (n + 1) - x n‖ ^ 2) ∧
    ((∀ (y : E) (k : ℕ → ℕ), StrictMono k → WeakTendsto (x ∘ k) y → y ∈ Z) →
      ∃ z ∈ Z, WeakTendsto x z) := by sorry

end SaddleSplit.Async
