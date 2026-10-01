-- Prove2me | Theorems.Thm_ShorAlgorithms_DiscreteLog_card_good_pairs_ge
-- name    : ShorAlgorithms.DiscreteLog.card_good_pairs_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T01:19:44.620923+00:00
-- url     : https://prove2.me/theorems/2e06fded-6b23-4064-b9df-ab684c6ea0b9
-- title:
--   §6, p. 1504 — at least $q/12$ pairs $(c,d)$ are good
-- statement:
--   Let $p$ be a prime, $0\le r<p-1$, and $q=2^l$ a power of $2$ with $p<q<2p$. Then the number of pairs $(c,d)$ with $0\le c,d<q$ satisfying both conditions (6.10) and (6.11) is at least $q/12$:
--
--   $$
--   \#\{(c,d)\in\{0,\dots,q-1\}^2 : (c,d)\ \text{is good}\}\ \ge\ \frac{q}{12}.
--   $$
--
--   Together with the lower bound on the probability of each good state, this count yields a constant lower bound on the probability of a good output.
--
--   **Formalization Note** The page asserts that for every $c$ there is *exactly one* $d$ satisfying (6.10); this can fail at a tie $\{T\}_q=\pm\frac12$, where two values of $d$ qualify. Only the count is stated here, which needs at least one such $d$ per $c$.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1504, §6 ("We will now count the number of pairs $(c, d)$ …")

import Mathlib
import Definitions.Def_ShorAlgorithms_DiscreteLog_IsGood

namespace ShorAlgorithms.DiscreteLog

open Classical in
/-- Shor (1997), §6, p. 1504 ("We will now count the number of pairs"): under the hypotheses
of §6, at least `q/12` pairs `(c, d)` with `0 ≤ c, d < q` satisfy (6.10) and (6.11). -/
theorem card_good_pairs_ge (p : ℕ) [hp : Fact p.Prime] (r : ℕ) (hr : r < p - 1)
    (q l : ℕ) (hq : q = 2 ^ l) (hpq : p < q) (hqp : q < 2 * p) :
    (q : ℝ) ≤ 12 * ((Finset.univ.filter
      (fun cd : Fin q × Fin q => IsGood p q r cd.1 cd.2)).card : ℝ) := by sorry

end ShorAlgorithms.DiscreteLog
