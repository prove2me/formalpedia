-- Prove2me | Theorems.Thm_TIEMaximin_proposition_5_3
-- name    : TIEMaximin.proposition_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:48:47.844305+00:00
-- url     : https://prove2.me/theorems/8ebd51b4-d616-47a7-823a-1cd00afe81cc
-- title:
--   Proposition 5.3 — every realized allocation gives at least $\mathrm{TPS}_i/6$
-- statement:
--   Let $m\ge n\ge2$ and let $v$ be a nonnegative profile. Every allocation in the support of every lottery of the mechanism of §4.4 at $v$ gives every agent $i$ value at least $\mathrm{TPS}_i/6$.
--
--   This is the ex-post half of Theorem 1.1 for $m\ge n\ge2$, stated for allocations and not in expectation.
--
--   Differences from the source:
--   - reading: the lottery of the mechanism (§4.4) → every `L` with `IsMechLottery v L`: any order of D with k nondecreasing, any lotteries with the properties of Lemmas 4.1 and 4.3, any completion with the conditional probabilities e_ig/e_g; reason: §4.4 fixes these only through their properties, and Lemma 4.4's proof allows any such joint distribution; `mechanism_exists` states that such an L exists
--   - encoding: agents N, goods M, nonnegative additive valuations → `Fin n`, `Fin m` (0-based), real matrices with the hypothesis `Nonneg`, bundle value `valOf`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Proposition 5.3, p.23

import Mathlib
import Definitions.Def_TIEMaximin_MechLottery

namespace TIEMaximin

/-- **Proposition 5.3** (p.23). Every allocation in the support of the mechanism gives every agent `i`
value at least `TPS_i/6`.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Proposition 5.3, p.23.

**Formalization Note.** Stated for every lottery the mechanism of §4.4 can produce
(`IsMechLottery`), completion step included. -/
theorem proposition_5_3 {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (v : Fin n → Fin m → ℝ) (hv : Nonneg v)
    (L : PMF (Alloc n m)) (hL : IsMechLottery v L) :
    ∀ A ∈ L.support, ∀ i, tps n (v i) / 6 ≤ valOf (v i) i A := by sorry

end TIEMaximin
