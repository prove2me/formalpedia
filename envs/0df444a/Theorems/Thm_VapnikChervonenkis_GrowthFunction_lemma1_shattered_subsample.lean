-- Prove2me | Theorems.Thm_VapnikChervonenkis_GrowthFunction_lemma1_shattered_subsample
-- name    : VapnikChervonenkis.GrowthFunction.lemma1_shattered_subsample
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:36:04.956673+00:00
-- url     : https://prove2.me/theorems/7fcfb085-7bf9-4ee7-8119-0818ff446014
-- title:
--   Lemma 1 — Δ^S ≥ Φ(n, i) forces a subsample of size n with index 2^n
-- statement:
--   Let $X$ be a set, $S$ a collection of subsets of $X$, and $\Phi$ the function defined by the recurrence (1). Suppose that for some sample $x_1, \dots, x_i$ of size $i$ and some number $n$ with $1 \le n \le i$,
--
--   $$
--   \Delta^S(x_1, \dots, x_i) \ge \Phi(n, i).
--   $$
--
--   Then there exists a subsample $x_{i_1}, \dots, x_{i_n}$ of this sample, with positions $i_1 < \dots < i_n$, such that
--
--   $$
--   \Delta^S(x_{i_1}, \dots, x_{i_n}) = 2^n ,
--   $$
--
--   that is, the sets of $S$ induce all $2^n$ subsamples of $x_{i_1}, \dots, x_{i_n}$.
--
--   This is the paper's form of the Sauer–Shelah lemma. Its contrapositive drives Theorem 1: if no subsample of size $n$ has index $2^n$, then every sample of size $i \ge n$ has index below $\Phi(n, i)$.
--
--   **Formalization Note.** Samples are functions `Fin i → X`. The subsample is `x ∘ e` for a strictly increasing `e : Fin n → Fin i`, so it consists of $n$ distinct positions of the sample (the points at those positions may coincide, in which case its index is below $2^n$). The range $1 \le n \le i$ is part of the hypothesis, as in the paper.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 266, Lemma 1

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_Phi
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction

namespace VapnikChervonenkis.GrowthFunction

/-- **Lemma 1** of Vapnik and Chervonenkis (1971), p. 266: if for some sample `x_1, ···, x_i` of
size `i` and some number `n` with `1 ≤ n ≤ i` one has `Δ^S(x_1, ···, x_i) ≥ Φ(n, i)`, then there is
a subsample `x_{i_1}, ···, x_{i_n}` of this sample (positions `i_1 < ··· < i_n`) with
`Δ^S(x_{i_1}, ···, x_{i_n}) = 2^n`. -/
theorem lemma1_shattered_subsample {X : Type*} (S : Set (Set X)) (i n : ℕ) (x : Fin i → X)
    (hn1 : 1 ≤ n) (hni : n ≤ i) (hΔ : Shared.Phi n i ≤ Shared.index S x) :
    ∃ e : Fin n → Fin i, StrictMono e ∧ Shared.index S (x ∘ e) = 2 ^ n := by sorry

end VapnikChervonenkis.GrowthFunction
