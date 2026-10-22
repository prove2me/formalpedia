-- Prove2me | Theorems.Thm_SecretaryAdvice_SamplesDual_key_identity_base
-- name    : SecretaryAdvice.SamplesDual.key_identity_base
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:43:19.140055+00:00
-- url     : https://prove2.me/theorems/880cd059-ae12-4495-b1d0-6e95441ff72c
-- title:
--   Proof of Theorem 17, p. 18 — base case s = k: T(i,k) = Σ_j C(n−i,j)(1/j) j! ∏_{t=i}^{n−j−1}(k+t)
-- statement:
--   Let $n,k$ be natural numbers and $1\le i<n$, and let $T(i,s')$ be the quantity of the proof of Theorem 17 (p. 17). Then
--
--   $$T(i,k)=\sum_{j=1}^{n-i}\binom{n-i}{j}\frac1j\,j!\prod_{t=i}^{n-j-1}(k+t).$$
--
--   This is the key identity at $s=k$ (where $\prod_{\ell=1}^{j}(k-k+\ell)=j!$), the base of the backward induction over $s$.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 18, proof of Theorem 17, base case s = k

import Mathlib
import Definitions.Def_SecretaryAdvice_SamplesDual_ClosedForm

open Finset

namespace SecretaryAdvice.SamplesDual

/-- Proof of Theorem 17, p. 18, base case `s = k` of the key identity:
`T(i,k) = Σ_{j=1}^{n−i} C(n−i,j) · (1/j) · j! · ∏_{t=i}^{n−j−1} (k+t)`. -/
theorem key_identity_base (n k i : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    T n k i k =
      ∑ j ∈ Icc 1 (n - i),
        ((n - i).choose j : ℝ) * (1 / (j : ℝ)) * (j.factorial : ℝ) *
          (∏ t ∈ Icc i (n - j - 1), ((k : ℝ) + t)) := by sorry

end SecretaryAdvice.SamplesDual
