-- Prove2me | Theorems.Thm_QuasiPolyTrace_lemma_19
-- name    : QuasiPolyTrace.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:31:54.569503+00:00
-- url     : https://prove2.me/theorems/f9126650-18ca-41b7-a80a-f6b218e48d65
-- title:
--   Lemma 19 — a product of three statistics is a mixture at retention $1-(1-p)^3$
-- statement:
--   Let $p\in[0,1]$, $P=1-(1-p)^3$, and let $s_1,s_2,s_3$ be statistics. There are nonnegative coefficients $\alpha(S)$, indexed by statistics $S$ and depending only on $p,s_1,s_2,s_3$, with $\alpha(S)=0$ unless $|S|\le|s_1|+|s_2|+|s_3|$, such that for every binary string $x$
--
--   $$
--   x^{(s_1)}_p\,x^{(s_2)}_p\,x^{(s_3)}_p=\sum_S\alpha(S)\,x^{(S)}_P .
--   $$
--
--   Three independent traces with retention $p$ can be simulated from one trace with retention $P$; this turns the summed triple products of Lemma 16 back into single statistics of order at most $3k$ (Lemma 36).
--
--   Differences from the source:
--   - generalization: a linear combination with nonnegative coefficients α_{s1,s2,s3}(S) → additionally α(S) = 0 unless |S| ≤ |s1| + |s2| + |s3|; reason: the sentence before the lemma (p.21) states the order bound ("statistics of order at most 3k"); the Lean statement implies the printed one
--   - reading: α_{s1,s2,s3}(S), x not quantified → one α, chosen before x, for every binary string x of every length; reason: the subscript shows α depends on the three statistics (and p) only; the proof's α is a probability of the simulation, independent of x
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 19, p.21, with the sentence before it (order at most 3k)

import Mathlib
import Definitions.Def_QuasiPolyTrace_stat

namespace QuasiPolyTrace

/-- **Lemma 19 (a product of three statistics is a nonnegative combination of statistics at a higher
retention probability).** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 19, p.21: "Let P = 1 − (1 − p)³. Given three statistics s1, s2, s3
we can express x^{(s1)}_p x^{(s2)}_p x^{(s3)}_p as a linear combination ∑_S α(S) x^{(S)}_P with
nonnegative coefficients α_{s1,s2,s3}(S)." The sentence before it (p.21): "each term in Equation 8 can be
written as a linear combination of statistics of order at most 3k."

**Formalization Note.**
* The coefficients `α` are chosen before the string `x` (the subscript `α_{s1,s2,s3}`: they depend on
  `p` and the three statistics only), and serve every binary string `x` of every length.
* `α S ≠ 0` only for statistics of order at most `|s1| + |s2| + |s3|`: the "order at most 3k" of the
  preceding sentence, for three statistics of order at most `k`.
* `α` need not have finite support; for a fixed `x` only the finitely many `S ⊆ {1, …, |x|}` have
  `x^{(S)}_P ≠ 0`, so the `tsum` is a finite sum.
* `p ∈ [0, 1]` is the standing assumption that `p` is a retention probability. -/
theorem lemma_19 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s₁ s₂ s₃ : Finset ℤ) :
    ∃ α : Finset ℤ → ℝ, (∀ S, 0 ≤ α S) ∧
      (∀ S, α S ≠ 0 → S.card ≤ s₁.card + s₂.card + s₃.card) ∧
      ∀ x : List Bool, stat p x s₁ * stat p x s₂ * stat p x s₃ =
        ∑' S : Finset ℤ, α S * stat (1 - (1 - p) ^ 3) x S := by sorry

end QuasiPolyTrace
