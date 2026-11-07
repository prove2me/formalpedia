-- Prove2me | Theorems.Thm_TIEMaximin_proposition_3_2
-- name    : TIEMaximin.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:42:27.777662+00:00
-- url     : https://prove2.me/theorems/2d361f83-4b24-42db-b0e1-69f4f775ed0b
-- title:
--   Proposition 3.2 — implementing the rule gives incentives and ex-ante fairness
-- statement:
--   Let $m\ge n\ge2$. Any mechanism that implements the top-set competitive rule (5) at every nonnegative profile is truthful in expectation and ex-ante envy-free.
--
--   The incentives and the ex-ante fairness of the final mechanism come entirely from this statement, so the implementation may use the reported values freely.
--
--   Differences from the source:
--   - encoding: agents N, goods M, nonnegative additive valuations → `Fin n`, `Fin m` (0-based), real matrices with the hypothesis `Nonneg`, bundle value `valOf`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Proposition 3.2, p.11

import Mathlib
import Definitions.Def_TIEMaximin_Mechanism
import Definitions.Def_TIEMaximin_Rule

namespace TIEMaximin

/-- **Proposition 3.2** (p.11). Any mechanism that implements the top-set competitive rule (5) is
truthful-in-expectation and ex-ante envy-free.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Proposition 3.2, p.11.

**Formalization Note.** "Implements" is required at every nonnegative profile. `2 ≤ n ≤ m` is the
standing assumption (p.8). -/
theorem proposition_3_2 {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (M : Mech n m)
    (hM : ∀ v, Nonneg v → Implements (M v) (xRule v)) :
    IsTIE M ∧ IsExAnteEF M := by sorry

end TIEMaximin
