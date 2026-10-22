-- Prove2me | Theorems.Thm_SecretaryAdvice_SamplesDual_unclipped_closed_form
-- name    : SecretaryAdvice.SamplesDual.unclipped_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:43:28.141672+00:00
-- url     : https://prove2.me/theorems/95244bf8-5309-48dd-980f-ed70f59a3056
-- title:
--   Proof of Theorem 17, pp. 17–19 — the un-clipped dual recursion equals the formula of Theorem 17 without the max
-- statement:
--   Consider the secretary problem with $n$ secretaries and $k$ samples, and let $v(i,s)$ be the backward recursion of the dual LP with the samples coefficients of §5 and with the clipping $\max\{0,\cdot\}$ removed: $v(n,s)=a(n,s)$ and $v(i,s)=a(i,s)-\sum_{j>i}\sum_{s'}v(j,s')\,c(j,s',i,s)$. Then for every round $1\le i\le n$ and signal $s\in\{0,\dots,k\}$,
--
--   $$v(n,s)=\frac{1}{k+1}\prod_{t=1}^{n-1}\frac{s+t}{k+t+1},$$
--
--   and for $i<n$
--
--   $$v(i,s)=\frac{1}{k+1}\prod_{t=1}^{i-1}\frac{s+t}{k+t+1}\left(\prod_{t=i}^{n-1}\frac{s+t}{k+t+1}-\frac{\sum_{j=1}^{n-i}\binom{n-i}{j}\frac1j\prod_{\ell=1}^{j}(k-s+\ell)\prod_{\ell=1}^{n-i-j}(s+i-1+\ell)}{\prod_{t=i}^{n-1}(k+t+1)}\right).$$
--
--   This is what the paper's induction proves ("For the proof we can ignore the $\max\{0,\cdot\}$").
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, pp. 17–19, proof of Theorem 17 (with the max ignored)

import Mathlib
import Definitions.Def_SecretaryAdvice_SamplesDual_ClosedForm

open Finset

namespace SecretaryAdvice.SamplesDual

/-- Proof of Theorem 17, pp. 17–19, with `max {0, ·}` ignored: the un-clipped backward recursion
`v(i,s)` equals `a(n,s)` at `i = n` and the expression inside the max of Theorem 17 for `i < n`. -/
theorem unclipped_closed_form (n k i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (s : Fin (k + 1)) :
    samplesUnclipped n k i s = unclippedFormula n k i s := by sorry

end SecretaryAdvice.SamplesDual
