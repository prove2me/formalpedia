-- Prove2me | Theorems.Thm_TIEMaximin_lemma_3_10
-- name    : TIEMaximin.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:42:40.181304+00:00
-- url     : https://prove2.me/theorems/f966b303-e8d2-40b5-ba09-9c763da9c316
-- title:
--   Lemma 3.10 — parameters of a deficient agent
-- statement:
--   Let $m\ge n\ge2$, $\alpha\in(0,1)$, and let $v$ be a nonnegative profile. For every deficient agent $i$,
--
--   $$H_i\subseteq T_i,\qquad q_i=a_i-\frac{\sum_{g\in H_i}(n-f_g)}{n-1},\qquad 1\le a_i\le n,\qquad 0<q_i\le a_i.$$
--
--   These relations connect the deficiency $q_i$ to nominations, and they are used in all the counting bounds.
--
--   Differences from the source:
--   - encoding: agents N, goods M, nonnegative additive valuations → `Fin n`, `Fin m` (0-based), real matrices with the hypothesis `Nonneg`, bundle value `valOf`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Lemma 3.10, eq. (9), p.16

import Mathlib
import Definitions.Def_TIEMaximin_Basic
import Definitions.Def_TIEMaximin_Deficient

namespace TIEMaximin

/-- **Lemma 3.10** (p.16). For every deficient agent `i`, `H_i ⊆ T_i`, `q_i = a_i − (Σ_{g∈H_i}(n −
f_g))/(n − 1)`, `1 ≤ a_i ≤ n`, and `0 < q_i ≤ a_i` (9).

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Lemma 3.10, eq. (9), p.16.

**Formalization Note.** Stated for every `α ∈ (0,1)` (p.10). -/
theorem lemma_3_10 {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (v : Fin n → Fin m → ℝ) (hv : Nonneg v) (i : Fin n) (hi : IsDeficient α v i) :
    high α v i ⊆ topSet v i ∧
    qDef α v i = (aDef α v i : ℝ) -
      (∑ g ∈ high α v i, ((n : ℝ) - (nom v g : ℝ))) / ((n : ℝ) - 1) ∧
    1 ≤ aDef α v i ∧ aDef α v i ≤ n ∧
    0 < qDef α v i ∧ qDef α v i ≤ (aDef α v i : ℝ) := by sorry

end TIEMaximin
