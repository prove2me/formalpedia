-- Prove2me | Theorems.Thm_TIEMaximin_corollary_5_2
-- name    : TIEMaximin.corollary_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:48:21.474931+00:00
-- url     : https://prove2.me/theorems/02e711b0-f112-422d-aa53-7f3b340a5b74
-- title:
--   Corollary 5.2 — the mechanism is TIE and ex-ante envy-free
-- statement:
--   Let $m\ge n\ge2$. Every mechanism whose output at each nonnegative profile is a lottery of the mechanism of §4.4 is truthful in expectation and ex-ante envy-free.
--
--   This is the ex-ante half of Theorem 1.1 for $m\ge n\ge2$.
--
--   Differences from the source:
--   - reading: the lottery of the mechanism (§4.4) → every `L` with `IsMechLottery v L`: any order of D with k nondecreasing, any lotteries with the properties of Lemmas 4.1 and 4.3, any completion with the conditional probabilities e_ig/e_g; reason: §4.4 fixes these only through their properties, and Lemma 4.4's proof allows any such joint distribution; `mechanism_exists` states that such an L exists
--   - encoding: agents N, goods M, nonnegative additive valuations → `Fin n`, `Fin m` (0-based), real matrices with the hypothesis `Nonneg`, bundle value `valOf`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Corollary 5.2, p.23

import Mathlib
import Definitions.Def_TIEMaximin_Mechanism
import Definitions.Def_TIEMaximin_MechLottery

namespace TIEMaximin

/-- **Corollary 5.2** (p.23). The mechanism is truthful-in-expectation and ex-ante envy-free.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Corollary 5.2, p.23.

**Formalization Note.** Stated for every selection `M` of lotteries of the mechanism of §4.4 at
nonnegative profiles. -/
theorem corollary_5_2 {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (M : Mech n m)
    (hM : ∀ v, Nonneg v → IsMechLottery v (M v)) :
    IsTIE M ∧ IsExAnteEF M := by sorry

end TIEMaximin
