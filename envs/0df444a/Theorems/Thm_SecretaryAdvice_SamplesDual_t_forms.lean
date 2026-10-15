-- Prove2me | Theorems.Thm_SecretaryAdvice_SamplesDual_t_forms
-- name    : SecretaryAdvice.SamplesDual.t_forms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:43:20.662182+00:00
-- url     : https://prove2.me/theorems/90556f71-23d9-48a4-9fbf-d6723959f69b
-- title:
--   Proof of Theorem 17, pp. 17–18 — two forms of T(i,s′)
-- statement:
--   Let $n,k$ be natural numbers, $1\le i<n$ and $0\le s'\le k$, and let $T(i,s')$ be the quantity defined in the proof of Theorem 17 (p. 17),
--
--   $$T(i,s')=(n-i)\prod_{t=i+1}^{n-1}(s'+t)-\sum_{z=i+1}^{n-1}\sum_{j=1}^{n-z}\binom{n-z}{j}\frac1j\prod_{\ell=1}^{j}(k-s'+\ell)\prod_{t=i+1}^{n-j-1}(s'+t).$$
--
--   Then
--
--   $$T(i,s')=(n-i)\prod_{t=i+1}^{n-1}(s'+t)-\sum_{j=1}^{n-i-1}(n-i)\binom{n-i-1}{j}\frac{1}{j(j+1)}\prod_{\ell=1}^{j}(k-s'+\ell)\prod_{t=i+1}^{n-j-1}(s'+t).$$
--
--   The second form collapses the double sum over $z$ and $j$ into a single sum over $j$; it is the form in which the base case and the inductive step of the key identity are carried out.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, pp. 17–18, proof of Theorem 17, the three displayed expressions of T(i, s′) (first = last)

import Mathlib
import Definitions.Def_SecretaryAdvice_SamplesDual_ClosedForm

open Finset

namespace SecretaryAdvice.SamplesDual

/-- Proof of Theorem 17, pp. 17–18: the first and the last displayed expressions of `T(i,s')`
agree:
`T(i,s') = (n−i) ∏_{t=i+1}^{n−1} (s'+t)
  − Σ_{j=1}^{n−i−1} (n−i) · C(n−i−1,j) · 1/(j(j+1)) · ∏_{ℓ=1}^{j} (k−s'+ℓ) · ∏_{t=i+1}^{n−j−1} (s'+t)`. -/
theorem t_forms (n k i s' : ℕ) (hi : 1 ≤ i) (hin : i < n) (hs : s' ≤ k) :
    T n k i s' =
      ((n : ℝ) - i) * (∏ t ∈ Icc (i + 1) (n - 1), ((s' : ℝ) + t)) -
        ∑ j ∈ Icc 1 (n - i - 1),
          ((n : ℝ) - i) * ((n - i - 1).choose j : ℝ) * (1 / ((j : ℝ) * ((j : ℝ) + 1))) *
            (∏ ℓ ∈ Icc 1 j, ((k : ℝ) - s' + ℓ)) *
            (∏ t ∈ Icc (i + 1) (n - j - 1), ((s' : ℝ) + t)) := by sorry

end SecretaryAdvice.SamplesDual
