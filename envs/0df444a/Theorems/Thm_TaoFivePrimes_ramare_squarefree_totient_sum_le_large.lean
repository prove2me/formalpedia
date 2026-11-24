-- Prove2me | Theorems.Thm_TaoFivePrimes_ramare_squarefree_totient_sum_le_large
-- name    : TaoFivePrimes.ramare_squarefree_totient_sum_le_large
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T08:18:11.06225+00:00
-- url     : https://prove2.me/theorems/017351d0-907f-4262-b614-6850111f1ff0
-- title:
--   Ramaré's squarefree totient sum: analytic range $z \ge 142300$
-- statement:
--   Let $G(z) = \sum_{n \le z} \mu^2(n)/\varphi(n)$ denote the summatory function of the squarefree totient weights. For every integer $N \ge 142300$,
--   $$G(N) \;\le\; \log N + 1.4708.$$
--   This is the analytic component of Lemma 3.5(1) of Ramaré's 1995 paper on Šnirel'man's constant, the estimate used by Tao in the proof of Proposition 4.10 on the mesoscopic sifted pair correlation. Ramaré bounds the error in the asymptotic expansion of $G$ (his Lemma 3.2), re-run with the exponent $0.45$ in place of $1/3$, by $0.138217\ldots = 1.4708 - 1.332583$; equations (3.10)–(3.12) reduce this to an explicit numerical condition involving the Chebyshev bound $\theta(t) \le 1.001093\,t$, satisfied as soon as $z \ge 142300$. The complementary range $1 \le z \le 142300$ is handled separately by direct verification (eq. (3.13)).
--
--   Formalization note: the sum is a finite sum over `Finset.Icc 1 N` of the indicator `Squarefree n` divided by `Nat.totient n`, which agrees with $G(N)$ at integer points.
-- source:
--   O. Ramaré, *On Shnirel'man's constant*, Annali della Scuola Normale Superiore di Pisa, Classe di Scienze (4) 22 (1995), 645–706, http://www.numdam.org/item/ASNSP_1995_4_22_4_645_0/, Lemma 3.5(1) and proof, pp. 659–660, eqs. (3.10)–(3.12); used in T. Tao, *Every odd number greater than 1 is the sum of at most five primes*, arXiv:1201.6656, https://arxiv.org/abs/1201.6656, proof of Proposition 4.10.

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped BigOperators

namespace TaoFivePrimes

theorem ramare_squarefree_totient_sum_le_large (N : ℕ) (hN : 142300 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
      if Squarefree n then (1 : ℝ) / Nat.totient n else 0) ≤
      Real.log (N : ℝ) + 1.4708 := by sorry

end TaoFivePrimes
