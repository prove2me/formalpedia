-- Prove2me | Theorems.Thm_SaddleSplit_Async_lemma_A_3
-- name    : SaddleSplit.Async.lemma_A_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:28.566212+00:00
-- url     : https://prove2.me/theorems/6caead49-58ea-4a35-9229-635a09a9a8e2
-- title:
--   Lemma A.3, p. 31 — square-summable increments with covering windows and bounded lags give x_{ϑ_i(n)} − x_n → 0
-- statement:
--   Let $I$ be a nonempty finite set, $(I_n)_{n\in\mathbb N}$ nonempty subsets of $I$, $P\in\mathbb N$, and $(x_n)_{n\in\mathbb N}$ a sequence in a real Hilbert space $\mathcal K$. Suppose that $\sum_n\|x_{n+1}-x_n\|^2<+\infty$, $I_0=I$ and $\bigcup_{j=n}^{n+P}I_j=I$ for every $n$. Let $T\in\mathbb N$, $i\in I$, and let $(\pi_i(n))_{n\in\mathbb N}$ be a sequence in $\mathbb N$ with $n-T\le\pi_i(n)\le n$. Set
--   $$\overline\vartheta_i(n)=\max\{j\in\mathbb N\mid j\le n\ \text{and}\ i\in I_j\},\qquad \vartheta_i(n)=\pi_i(\overline\vartheta_i(n)).$$
--   Then $x_{\vartheta_i(n)}-x_n\to0$.
--
--   In Algorithm 3.4, $\vartheta_i(n)$ is the iteration whose data block $i$ last used; the lemma shows that this stale information becomes asymptotically current.
--
--   **Formalization Note** $\overline\vartheta_i(n)$ is `Nat.findGreatest (fun j => i ∈ I j) n`; since $I_0=I$ the set is nonempty and this is the true maximum. The lag condition is written $\pi_i(n)\le n\le\pi_i(n)+T$ to avoid natural-number subtraction.
-- source:
--   Bùi & Combettes, Multivariate monotone inclusions in saddle form, arXiv:2002.06135v3, p. 31, Lemma A.3

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting

namespace SaddleSplit.Async
open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

/-- Lemma A.3, p. 31: with square-summable increments, blocks covering `I` within every window of
length `P + 1`, and lags at most `T`, `x_{ϑ_i(n)} − x_n → 0`, where
`ϑ̄_i(n) = max{j ≤ n | i ∈ I_j}` and `ϑ_i(n) = π_i(ϑ̄_i(n))`. -/
theorem lemma_A_3 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (In : ℕ → Finset I) (hIn : ∀ n, (In n).Nonempty) (Pw : ℕ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : ℕ → E) (hx : Summable fun n => ‖x (n + 1) - x n‖ ^ 2)
    (h0 : In 0 = Finset.univ)
    (hcov : ∀ n, (Finset.range (Pw + 1)).biUnion (fun j => In (n + j)) = Finset.univ)
    (T : ℕ) (i : I) (π : ℕ → ℕ) (hπ : ∀ n, π n ≤ n ∧ n ≤ π n + T) :
    Tendsto (fun n => x (π (Nat.findGreatest (fun j => i ∈ In j) n)) - x n) atTop
      (𝓝 0) := by sorry

end SaddleSplit.Async
