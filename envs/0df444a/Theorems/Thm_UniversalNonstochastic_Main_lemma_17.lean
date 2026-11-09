-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_lemma_17
-- name    : UniversalNonstochastic.Main.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:05:25.726459+00:00
-- url     : https://prove2.me/theorems/da413aaf-2da5-4a28-a10e-3b8b6d5a848f
-- title:
--   Lemma 17 — the universal measure dominates its composition with a computable kernel
-- statement:
--   Let $\mathbf m$ be a universal semimeasure on $\mathbb N=\{1,2,\dots\}$ and let $(\kappa_n)_{n\in\mathbb N}$ be probability measures on $\mathbb N$ whose atom masses $(n,i)\mapsto\kappa_n(\{i\})$ form a computable real function of the pair $(n,i)$. Then there is a constant $c_\kappa>0$ such that, for every subset $A\subseteq\mathbb N$,
--   $$\mathbf m(A)\;\ge\;c_\kappa\sum_{n\in\mathbb N}\mathbf m(n)\,\kappa_n(A).$$
--
--   The constant depends only on the kernel (and the fixed $\mathbf m$), and the inequality holds for arbitrary, not necessarily decidable, sets $A$. The lemma is the basic tool of Sect. A.1: Lemma 3 and Lemma 18 are applications of it with particular kernels.
--
--   **Formalization Note** $\kappa_n$ is given by its atom masses, nonnegative and summing to $1$, and $\kappa_n(A)=\sum_{i\in A}\kappa_n(\{i\})$. Computability means uniform rational approximation within $2^{-k}$.
--
--   Differences from the source:
--   - encoding: m: a fixed universal semimeasure on ℕ, m(A) = Σ_{a∈A} m(a) → m : UniversalSemimeasure (arbitrary), mass m A = real tsum of the indicator; reason: the weights are nonnegative with partial sums ≤ 1, so the real sum is the true sum; the statement is quantified over every universal semimeasure
--   - encoding: probability measures κ_n on ℕ with (n,i) ↦ κ_n({i}) computable → κ : ℕ+ → ℕ+ → ℝ nonnegative with HasSum (κ n) 1 and IsComputableRealFun of the pair (n, i); reason: a probability measure on the discrete space ℕ is determined by its atoms; computability of a real-valued map is uniform rational approximation
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/11.pdf, Lemma 17, p.15 (PDF p.15)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Effective
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure

namespace UniversalNonstochastic.Main

/-- Lemma 17, p.15: for a computable kernel `(κₙ)` of probability measures on `ℕ`, the
universal measure dominates the composition `∑ₙ m(n) κₙ(·)` up to a constant `c_κ > 0`,
on every subset `A ⊆ ℕ`. -/
theorem lemma_17 (m : UniversalSemimeasure) (κ : ℕ+ → ℕ+ → ℝ)
    (hκ_nonneg : ∀ n i, 0 ≤ κ n i) (hκ_prob : ∀ n, HasSum (κ n) 1)
    (hκ_comp : IsComputableRealFun fun p : ℕ+ × ℕ+ => κ p.1 p.2) :
    ∃ cκ : ℝ, 0 < cκ ∧ ∀ A : Set ℕ+,
      cκ * ∑' n : ℕ+, m.w n * ∑' i : ℕ+, A.indicator (κ n) i ≤ mass m A := by sorry

end UniversalNonstochastic.Main
