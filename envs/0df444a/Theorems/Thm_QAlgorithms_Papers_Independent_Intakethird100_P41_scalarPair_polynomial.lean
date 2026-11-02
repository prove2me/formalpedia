-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P41_scalarPair_polynomial
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P41.scalarPair_polynomial
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:55:55.57988+00:00
-- url     : https://prove2.me/theorems/1787b999-da82-4121-bc65-47962f67c263
-- title:
--   Explicit polynomial sine sum and its replica-one root
-- statement:
--   Fix a positive integer $k=2d$, so $d$ may be a positive half-integer. In the polynomial ring $\mathbb R[X]$, define the formal series
--
--   $$
--   B(X,u)=\sum_{m\ge0}\frac{\prod_{j=1}^{m}(X-j)}{(m+1)!}u^m,
--   \qquad
--   P_k(X)=(-1)^{k+1}[u^{2k}]\frac{(1+u)^{k-1}}{B(X,u)}.
--   $$
--
--   The empty product is one, so $B(X,0)=1$ and its formal inverse exists. Then $P_k$ has degree exactly $2k$, $P_k(1)=0$, and for every integer $n\ge1$,
--
--   $$
--   P_k(n)=\sum_{j=1}^{n-1}\left(2\sin\frac{\pi j}{n}\right)^{-2k}
--   =(-1)^{k+1}[u^{2k}]\frac{(1+u)^{k-1}}{\sum_{m\ge0}\binom n{m+1}u^m/n}.
--   $$
--
--   The latter coefficient is the coefficient of $u^{2k-1}$ in $(-1)^{k+1}n(1+u)^{k-1}/((1+u)^n-1)$, equivalently minus the residue at $t=1$ of $n/[t(1-t)^k(1-t^{-1})^k(t^n-1)]$. The specified scalar-pair continuation
--
--   $$
--   C_k(t)=\frac{P_k(t)}{2t^{2k-1}},\qquad t>0,
--   $$
--
--   is analytic, vanishes at $t=1$, and at positive integers equals $\tfrac12n^{1-2k}$ times the sine sum. This gives the continuation used for the scalar-pair contribution in the replica calculation. It asserts no uniqueness among arbitrary analytic interpolations.
-- source:
--   Entanglement Renyi entropies in holographic theories, arXiv:1006.0047v3, PDF p. 36, Appendix A.2, (A.22)–(A.25)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P41

namespace QAlgorithms.Papers.Independent.Intakethird100.P41

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open scoped Topology

/-- PDF pp.36-37, (A.22)-(A.25): for positive integer k=2d the sine sum is the
explicit residue polynomial of degree exactly 2k=4d, with a root at n=1. Its rational
scalar-pair continuation is analytic on positive real replica index and vanishes at one.
No CFT, unique analytic-continuation, or all-replica-root claim is assumed. -/
theorem scalarPair_polynomial (k : ℕ) (hk : 0 < k) :
    (sineSumPolynomial k).natDegree = 2 * k ∧
    (sineSumPolynomial k).eval 1 = 0 ∧
    (∀ n : ℕ, 1 ≤ n →
      (sineSumPolynomial k).eval (n : ℝ) = cosecantPowerSum k n ∧
      (sineSumPolynomial k).eval (n : ℝ) = residueCoefficient k n ∧
      scalarPairContinuation k (n : ℝ) =
        cosecantPowerSum k n / (2 * (n : ℝ) ^ (2 * k - 1))) ∧
    AnalyticOnNhd ℝ (scalarPairContinuation k) (Set.Ioi 0) ∧
    scalarPairContinuation k 1 = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P41
