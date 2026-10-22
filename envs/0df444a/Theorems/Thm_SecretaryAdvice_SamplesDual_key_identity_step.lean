-- Prove2me | Theorems.Thm_SecretaryAdvice_SamplesDual_key_identity_step
-- name    : SecretaryAdvice.SamplesDual.key_identity_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:43:17.020527+00:00
-- url     : https://prove2.me/theorems/1768ff51-25cd-48a8-b637-ac71e8a5469a
-- title:
--   Appendix B, pp. 26–28 — inductive step: the key identity at s + 1 implies it at s
-- statement:
--   Let $n,k$ be natural numbers, $1\le i<n$ and $0\le s<k$, let $T(i,s')$ be the quantity of the proof of Theorem 17, and write
--
--   $$R(i,s)=\sum_{j=1}^{n-i}\binom{n-i}{j}\frac1j\prod_{\ell=1}^{j}(k-s+\ell)\prod_{t=i}^{n-j-1}(s+t).$$
--
--   If $\sum_{s'=s+1}^{k}T(i,s')=R(i,s+1)$, then
--
--   $$\sum_{s'=s}^{k}T(i,s')=R(i,s).$$
--
--   Together with the base case $s=k$ this proves the key identity by backward induction over the signal $s$.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, pp. 26–28, Appendix B (Inductive Step in Proof of Theorem 17)

import Mathlib
import Definitions.Def_SecretaryAdvice_SamplesDual_ClosedForm

open Finset

namespace SecretaryAdvice.SamplesDual

/-- Appendix B, pp. 26–28, inductive step of the key identity: if it holds at `s + 1`, it holds
at `s` (for `1 ≤ i < n` and `0 ≤ s < k`). -/
theorem key_identity_step (n k i s : ℕ) (hi : 1 ≤ i) (hin : i < n) (hs : s < k)
    (h : ∑ s' ∈ Icc (s + 1) k, T n k i s' = keyRHS n k i (s + 1)) :
    ∑ s' ∈ Icc s k, T n k i s' = keyRHS n k i s := by sorry

end SecretaryAdvice.SamplesDual
