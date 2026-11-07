-- Prove2me | Theorems.Thm_TIEMaximin_lemma_3_12
-- name    : TIEMaximin.lemma_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:42:32.535984+00:00
-- url     : https://prove2.me/theorems/29b1d3fe-cba1-47d0-84c8-8ff42db85e1a
-- title:
--   Lemma 3.12 — retained mass on non-nominated edges
-- statement:
--   Let $m\ge n\ge2$, $\alpha\in(0,1)$, and let $v$ be a nonnegative profile. The total retained mass on non-nominated edges is at most one:
--
--   $$\sum_{i\in N}\sum_{g\in M\setminus T_i}h_{ig}\le1.$$
--
--   This controls the retained mass that the counting argument cannot charge to nominations.
--
--   Differences from the source:
--   - encoding: agents N, goods M, nonnegative additive valuations → `Fin n`, `Fin m` (0-based), real matrices with the hypothesis `Nonneg`, bundle value `valOf`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Lemma 3.12, p.17

import Mathlib
import Definitions.Def_TIEMaximin_Basic
import Definitions.Def_TIEMaximin_Deficient

namespace TIEMaximin

/-- **Lemma 3.12** (p.17). The total retained mass on non-nominated edges is at most one: `Σ_{i∈N}
Σ_{g∈M∖T_i} h_ig ≤ 1`.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Lemma 3.12, p.17.

**Formalization Note.** Stated for every `α ∈ (0,1)` (p.10). -/
theorem lemma_3_12 {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (v : Fin n → Fin m → ℝ) (hv : Nonneg v) :
    ∑ i, ∑ g ∈ Finset.univ \ topSet v i, hRet α v i g ≤ 1 := by sorry

end TIEMaximin
