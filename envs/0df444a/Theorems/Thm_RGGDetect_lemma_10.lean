-- Prove2me | Theorems.Thm_RGGDetect_lemma_10
-- name    : RGGDetect.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:38:19.154853+00:00
-- url     : https://prove2.me/theorems/4202e152-63e4-4d49-9092-f071d520b5d6
-- title:
--   Lemma 10 — the degree-weight generating function $F_{m,r}$
-- statement:
--   For any $r\le m\le n$ and every $0\le u\le1$,
--
--   $$
--   F_{m,r}(u)=\sum_{s=0}^r\binom ms\big(p+(1-p)u\big)^s\big(1-p+pu\big)^{m-s}. \tag{109}
--   $$
--
--   Moreover
--
--   $$
--   F^{(\ge K)}_{m,r}(u)\le\frac{(nu)^K}{K!}e^{nu},\qquad F_{m,r}(u)\le e^{nu}. \tag{110}
--   $$
--
--   Finally, for all sufficiently large $n$ and $r\le\lceil2np+100\log n\rceil+B^*$,
--
--   $$
--   F_{m,r}(1)=\sum_{s=0}^r\binom ms\le\exp\big(Cnp\log(1/p)\big). \tag{111}
--   $$
--
--   These are the elementary estimates behind Proposition 4.
--
--   **Formalization Note** (109)–(110) are stated for every $p\in[0,1]$ and every $K$. (111) is stated in the regime (1), with $C>0$ chosen after $\delta$ and $B^*$ and before the sequences, uniformly over $r\le m\le n$ in the range.
--
--   Differences from the source:
--   - generalization: the model's edge density p in (109)–(110) → every p ∈ [0, 1]; reason: the model's p lies in [0, 1]
--   - generalization: the standing hypotheses (1) of Theorem 1, for all n → sequences in `Regime δ p d τ`: each hypothesis for all large n; reason: the statement is asymptotic, so sequences satisfying (1) for all n are covered
--   - encoding: C a constant → C > 0 chosen after δ and B*, before the sequences; reason: the paper's convention on constants (p.2)
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Lemma 10, eqs. (109)–(111), p.29 (PDF p.31)

import Mathlib
import Definitions.Def_RGGDetect_Regime
import Definitions.Def_RGGDetect_fourierTail

open Filter Topology

namespace RGGDetect

/-- **Lemma 10** (degree-weight generating function; arXiv:2610.08517, held version, sha256 e7bebd4a…,
Lemma 10, p.29, eqs. (109)–(111)): for any `r ≤ m ≤ n` and every `0 ≤ u ≤ 1`,
`F_{m,r}(u) = ∑_{s=0}^{r} \binom ms (p + (1-p)u)^s (1 - p + pu)^{m-s}` (109);
moreover `F^{(≥K)}_{m,r}(u) ≤ ((nu)^K/K!) e^{nu}` and `F_{m,r}(u) ≤ e^{nu}` (110); finally, for all
sufficiently large `n` and `r ≤ ⌈2np + 100 log n⌉ + B*`,
`F_{m,r}(1) = ∑_{s=0}^{r} \binom ms ≤ exp(C n p log(1/p))` (111).

**Formalization Note** (109)–(110) are stated for every edge density `p ∈ [0, 1]` and every `K`.
(111) is stated in the regime (1): for every `δ > 0` and slack `B`, a constant `C` chosen before the
sequences, for all large `n`, uniformly over `r ≤ m ≤ n` in the range. -/
theorem lemma_10 :
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 → ∀ n m r K : ℕ, r ≤ m → m ≤ n → ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      Fgen p m r u = ∑ s ∈ Finset.range (r + 1),
          (m.choose s : ℝ) * (p + (1 - p) * u) ^ s * (1 - p + p * u) ^ (m - s) ∧
      FgenTail p m r K u ≤ ((n : ℝ) * u) ^ K / (K.factorial : ℝ) * Real.exp (n * u) ∧
      Fgen p m r u ≤ Real.exp (n * u)) ∧
    (∀ δ : ℝ, 0 < δ → ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℕ → ℝ) (d : ℕ → ℕ) (τ : ℕ → ℝ), Regime δ p d τ →
        ∀ᶠ n in atTop, ∀ m r : ℕ, r ≤ m → m ≤ n →
          r ≤ ⌈2 * (n : ℝ) * p n + 100 * Real.log n⌉₊ + B →
          Fgen (p n) m r 1 = ∑ s ∈ Finset.range (r + 1), (m.choose s : ℝ) ∧
          Fgen (p n) m r 1 ≤ Real.exp (C * n * p n * Real.log (1 / p n))) := by sorry

end RGGDetect
