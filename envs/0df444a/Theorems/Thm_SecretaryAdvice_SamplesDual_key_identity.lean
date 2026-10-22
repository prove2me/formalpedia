-- Prove2me | Theorems.Thm_SecretaryAdvice_SamplesDual_key_identity
-- name    : SecretaryAdvice.SamplesDual.key_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:43:15.546774+00:00
-- url     : https://prove2.me/theorems/6913e637-ef98-429e-84a2-95ada6969293
-- title:
--   Proof of Theorem 17, p. 18 — key identity Σ_{s′=s}^{k} T(i,s′) = Σ_j C(n−i,j)(1/j)∏_{ℓ≤j}(k−s+ℓ)∏_{t=i}^{n−j−1}(s+t)
-- statement:
--   Let $n,k$ be natural numbers, $1\le i<n$ and $0\le s\le k$, and let $T(i,s')$ be the quantity of the proof of Theorem 17 (p. 17). Then
--
--   $$\sum_{s'=s}^{k}T(i,s')=\sum_{j=1}^{n-i}\binom{n-i}{j}\frac1j\prod_{\ell=1}^{j}(k-s+\ell)\prod_{t=i}^{n-j-1}(s+t).$$
--
--   By the reduction step of the proof, this identity is exactly what is needed to establish the inductive step of Theorem 17 (with the maximum ignored).
--
--   **Formalization Note** The empty-product convention $\prod_{t=a}^{b}x_t=1$ for $b<a$ is used (the term $j=n-i$ has an empty product over $t$).
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 18, proof of Theorem 17 ("to establish the claim it suffices to show that")

import Mathlib
import Definitions.Def_SecretaryAdvice_SamplesDual_ClosedForm

open Finset

namespace SecretaryAdvice.SamplesDual

/-- Proof of Theorem 17, p. 18: for `1 ≤ i < n` and `0 ≤ s ≤ k`,
`Σ_{s'=s}^{k} T(i,s') = Σ_{j=1}^{n−i} C(n−i,j) · (1/j) · ∏_{ℓ=1}^{j} (k−s+ℓ) · ∏_{t=i}^{n−j−1} (s+t)`. -/
theorem key_identity (n k i s : ℕ) (hi : 1 ≤ i) (hin : i < n) (hs : s ≤ k) :
    ∑ s' ∈ Icc s k, T n k i s' = keyRHS n k i s := by sorry

end SecretaryAdvice.SamplesDual
