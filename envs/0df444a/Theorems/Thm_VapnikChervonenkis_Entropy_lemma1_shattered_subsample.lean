-- Prove2me | Theorems.Thm_VapnikChervonenkis_Entropy_lemma1_shattered_subsample
-- name    : VapnikChervonenkis.Entropy.lemma1_shattered_subsample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:08:44.709298+00:00
-- url     : https://prove2.me/theorems/4f73ca1d-dd3f-41da-8385-f8649fc02da0
-- title:
--   Lemma 1 — a sample with Δ^S ≥ Φ(n, i) has a subsample of size n with index 2^n
-- statement:
--   Let $S$ be a collection of subsets of a set $X$, let $x_1, \dots, x_i$ be a sample of size $i$, and let $n$ be a number with $1 \le n \le i$. If
--
--   $$
--   \Delta^S(x_1, \dots, x_i) \ge \Phi(n, i),
--   $$
--
--   where $\Phi$ is defined by the recurrence (1), then there is a subsample $x_{i_1}, \dots, x_{i_n}$ ($i_1 < \dots < i_n$) of this sample such that
--
--   $$
--   \Delta^S(x_{i_1}, \dots, x_{i_n}) = 2^n ,
--   $$
--
--   that is, $S$ induces all $2^n$ subsamples of it. This is the Sauer–Shelah lemma in the paper's sequence formulation; in the proof of necessity of Theorem 4 it provides, on a typical sample, a large subsample on which $S$ induces every subsample.
--
--   **Formalization Note.** The subsample is given by a strictly increasing map `e : Fin n → Fin i` of positions, and its terms are `x ∘ e`.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 266, Lemma 1

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_Phi
import Definitions.Def_VapnikChervonenkis_Shared_index

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- **Lemma 1** of Vapnik and Chervonenkis (1971), p. 266: if for some sample `x_1, ···, x_i` of
size `i` and some number `n` with `1 ≤ n ≤ i` one has `Δ^S(x_1, ···, x_i) ≥ Φ(n, i)`, then there is
a subsample `x_{i_1}, ···, x_{i_n}` of this sample (positions `i_1 < ··· < i_n`) with
`Δ^S(x_{i_1}, ···, x_{i_n}) = 2^n`. -/
theorem lemma1_shattered_subsample {X : Type*} (S : Set (Set X)) (i n : ℕ) (x : Fin i → X)
    (hn1 : 1 ≤ n) (hni : n ≤ i) (hΔ : Shared.Phi n i ≤ Shared.index S x) :
    ∃ e : Fin n → Fin i, StrictMono e ∧ Shared.index S (x ∘ e) = 2 ^ n := by sorry

end VapnikChervonenkis.Entropy
