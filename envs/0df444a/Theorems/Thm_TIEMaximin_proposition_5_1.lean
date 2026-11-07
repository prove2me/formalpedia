-- Prove2me | Theorems.Thm_TIEMaximin_proposition_5_1
-- name    : TIEMaximin.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:47:45.84942+00:00
-- url     : https://prove2.me/theorems/8d7c4616-0444-447a-bb80-1122d03e8ede
-- title:
--   Proposition 5.1 — the lottery of the mechanism implements $x$
-- statement:
--   Let $m\ge n\ge2$ and let $v$ be a nonnegative profile. Every lottery of the mechanism of §4.4 at $v$ implements the top-set competitive rule: agent $i$ receives good $g$ with probability exactly $x_{ig}$.
--
--   The final marginals are therefore independent of all the choices the mechanism makes after computing $x$.
--
--   Differences from the source:
--   - reading: the lottery of the mechanism (§4.4) → every `L` with `IsMechLottery v L`: any order of D with k nondecreasing, any lotteries with the properties of Lemmas 4.1 and 4.3, any completion with the conditional probabilities e_ig/e_g; reason: §4.4 fixes these only through their properties, and Lemma 4.4's proof allows any such joint distribution; `mechanism_exists` states that such an L exists
--   - reading: α (Sections 3 and 4) → α = 1/6; reason: Table 2: "α = 1/6 in this paper"
--   - encoding: agents N, goods M, nonnegative additive valuations → `Fin n`, `Fin m` (0-based), real matrices with the hypothesis `Nonneg`, bundle value `valOf`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Proposition 5.1, p.23

import Mathlib
import Definitions.Def_TIEMaximin_MechLottery

namespace TIEMaximin

/-- **Proposition 5.1** (p.23). The lottery of the mechanism implements `x`.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Proposition 5.1, p.23.

**Formalization Note.** Stated for every lottery the mechanism of §4.4 can produce
(`IsMechLottery`). -/
theorem proposition_5_1 {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (v : Fin n → Fin m → ℝ) (hv : Nonneg v)
    (L : PMF (Alloc n m)) (hL : IsMechLottery v L) :
    Implements L (xRule v) := by sorry

end TIEMaximin
