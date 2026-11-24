-- Prove2me | Theorems.Thm_TaoFivePrimes_ramare_squarefree_totient_sum_le_small
-- name    : TaoFivePrimes.ramare_squarefree_totient_sum_le_small
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T08:18:09.318198+00:00
-- url     : https://prove2.me/theorems/d69837d9-f165-45c0-a82c-bdb4d2efa4da
-- title:
--   Ramaré's squarefree totient sum: finite range $z \le 142300$
-- statement:
--   Let $G(z) = \sum_{n \le z} \mu^2(n)/\varphi(n)$. For every integer $1 \le N \le 142300$,
--   $$G(N) \;\le\; \log N + 1.4709.$$
--   This is the finite-range component of Lemma 3.5(1) of Ramaré (1995), the estimate used by Tao in the proof of Proposition 4.10. Ramaré proves the complementary large-$z$ range $z \ge 142300$ analytically, and then records (eq. (3.13)) the direct verification that the maximum of $G(z) - \log z$ over all $z \ge 1$ is attained at $z = 7$, where
--   $$G(7) - \log 7 = 1.470756\ldots \;\le\; 1.4709.$$
--   Thus the bound holds below the analytic threshold with a small margin; the extremal point is $N = 7$. Together with the analytic range, this yields Lemma 3.5(1) for all $z \ge 1$.
--
--   Formalization note: the sum is a finite sum over `Finset.Icc 1 N` of the indicator `Squarefree n` divided by `Nat.totient n`.
-- source:
--   O. Ramaré, *On Shnirel'man's constant*, Annali della Scuola Normale Superiore di Pisa, Classe di Scienze (4) 22 (1995), 645–706, http://www.numdam.org/item/ASNSP_1995_4_22_4_645_0/, Lemma 3.5(1) and proof, p. 660, eq. (3.13) (direct verification); used in T. Tao, *Every odd number greater than 1 is the sum of at most five primes*, arXiv:1201.6656, https://arxiv.org/abs/1201.6656, proof of Proposition 4.10.

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped BigOperators

namespace TaoFivePrimes

theorem ramare_squarefree_totient_sum_le_small (N : ℕ) (hN1 : 1 ≤ N)
    (hN2 : N ≤ 142300) :
    (∑ n ∈ Finset.Icc 1 N,
      if Squarefree n then (1 : ℝ) / Nat.totient n else 0) ≤
      Real.log (N : ℝ) + 1.4709 := by sorry

end TaoFivePrimes
