-- Prove2me | Theorems.Thm_TaoFivePrimes_ramare_squarefree_totient_sum_le
-- name    : TaoFivePrimes.ramare_squarefree_totient_sum_le
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T06:54:57.135803+00:00
-- url     : https://prove2.me/theorems/4cca70de-b24a-4fb8-8cca-8494530b81ec
-- title:
--   Ramaré's bound for the squarefree totient sum
-- statement:
--   For every $N \ge 1$, the sum of $\mu^2(n)/\varphi(n)$ over squarefree $n$ with $1 \le n \le N$ satisfies
--   $$\sum_{\substack{n \le N \\ n \text{ squarefree}}} \frac{\mu^2(n)}{\varphi(n)} \;\le\; \log N \;+\; 1.4709.$$
--   This is Ramaré's Lemma 3.5, used by Tao in the proof of Proposition 4.10. In the formal statement the indicator $\mu^2(n)$ is the condition `Squarefree n`, written as a finite sum over the interval $[1, N]$.
-- source:
--   O. Ramaré, *On Shnirel'man's constant*, Annali della Scuola Normale Superiore di Pisa, Classe di Scienze (4) 22 (1995), 645–706, Lemma 3.5, http://www.numdam.org/item/ASNSP_1995_4_22_4_645_0/; used in T. Tao, *Every odd number greater than 1 is the sum of at most five primes*, arXiv:1201.6656, https://arxiv.org/abs/1201.6656, proof of Proposition 4.10.

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped BigOperators

namespace TaoFivePrimes

theorem ramare_squarefree_totient_sum_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
      if Squarefree n then (1 : ℝ) / Nat.totient n else 0) ≤
      Real.log (N : ℝ) + 1.4709 := by sorry

end TaoFivePrimes
