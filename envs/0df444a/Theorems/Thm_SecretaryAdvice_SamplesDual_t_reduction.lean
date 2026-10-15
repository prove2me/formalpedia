-- Prove2me | Theorems.Thm_SecretaryAdvice_SamplesDual_t_reduction
-- name    : SecretaryAdvice.SamplesDual.t_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:43:22.815066+00:00
-- url     : https://prove2.me/theorems/5389691d-6fcb-4fe8-88a1-a19c5c8f9b5d
-- title:
--   Proof of Theorem 17, p. 17 — under the induction hypothesis, v(i,s) = a(n,s) − (1/(k+1))∏1/(k+t+1)·∏_{t<i}(s+t)·Σ_{s′≥s}T(i,s′)
-- statement:
--   Consider the secretary problem with $n$ secretaries and $k$ samples, and let $v(i,s)$ be the un-clipped backward recursion of the dual LP with the samples coefficients $a(i,s)$, $c(j,s',i,s)$ of §5. Let $1\le i<n$ and assume the inductive hypothesis of the proof of Theorem 17: for every round $i'$ with $i<i'\le n$ and every signal $s'\in\{0,\dots,k\}$, $v(i',s')$ equals the un-clipped closed form ($a(n,s')$ if $i'=n$, and the expression inside the maximum of Theorem 17 if $i'<n$). Then for every signal $s\in\{0,\dots,k\}$,
--
--   $$v(i,s)=\frac{1}{k+1}\prod_{t=1}^{n-1}\frac{s+t}{k+t+1}-\frac{1}{k+1}\prod_{t=1}^{n-1}\frac{1}{k+t+1}\cdot\prod_{t=1}^{i-1}(s+t)\cdot\sum_{s'=s}^{k}T(i,s'),$$
--
--   where $T(i,s')=(n-i)\prod_{t=i+1}^{n-1}(s'+t)-\sum_{z=i+1}^{n-1}\sum_{j=1}^{n-z}\binom{n-z}{j}\frac1j\prod_{\ell=1}^{j}(k-s'+\ell)\prod_{t=i+1}^{n-j-1}(s'+t)$.
--
--   This step reduces the inductive step of Theorem 17 to an identity about the sum $\sum_{s'=s}^k T(i,s')$.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 17, proof of Theorem 17, inductive step (first display and the definition of T(i, s′))

import Mathlib
import Definitions.Def_SecretaryAdvice_SamplesDual_ClosedForm

open Finset

namespace SecretaryAdvice.SamplesDual

/-- Proof of Theorem 17, p. 17: if the un-clipped recursion agrees with the claimed closed form
at every round `i' > i` and every signal, then at round `i`
`v(i,s) = 1/(k+1)·∏_{t=1}^{n−1} (s+t)/(k+t+1)
  − 1/(k+1)·∏_{t=1}^{n−1} 1/(k+t+1) · ∏_{t=1}^{i−1} (s+t) · Σ_{s'=s}^{k} T(i,s')`. -/
theorem t_reduction (n k i : ℕ) (hi : 1 ≤ i) (hin : i < n)
    (ih : ∀ i' : ℕ, i < i' → i' ≤ n → ∀ s' : Fin (k + 1),
      samplesUnclipped n k i' s' = unclippedFormula n k i' s')
    (s : Fin (k + 1)) :
    samplesUnclipped n k i s =
      1 / ((k : ℝ) + 1) * (∏ t ∈ Icc 1 (n - 1), (((s : ℕ) : ℝ) + t) / ((k : ℝ) + t + 1)) -
        1 / ((k : ℝ) + 1) * (∏ t ∈ Icc 1 (n - 1), 1 / ((k : ℝ) + t + 1)) *
          (∏ t ∈ Icc 1 (i - 1), (((s : ℕ) : ℝ) + t)) *
          ∑ s' ∈ Icc (s : ℕ) k, T n k i s' := by sorry

end SecretaryAdvice.SamplesDual
