-- Prove2me | Theorems.Thm_TIEMaximin_eq_22
-- name    : TIEMaximin.eq_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:42:50.981732+00:00
-- url     : https://prove2.me/theorems/bb9e9825-0fb7-4d04-a827-547a5d2dccc4
-- title:
--   Equation (22) — nominations on the low goods
-- statement:
--   Let $m\ge n\ge2$, $\alpha\in(0,1)$, and let $v$ be a nonnegative profile. For every deficient agent $i$,
--
--   $$\sum_{g\in L_i}f_g=n(a_i-1)+(n-1)(a_i-q_i).$$
--
--   This counts the nominations that land on an agent's low goods, and it feeds the bound of Case 1.
--
--   Differences from the source:
--   - generalization: displayed in Case 1 at α = 1/6 → every α ∈ (0,1), no case hypothesis; reason: the page's proof uses only Lemma 3.10, so this specializes to the source
--   - encoding: agents N, goods M, nonnegative additive valuations → `Fin n`, `Fin m` (0-based), real matrices with the hypothesis `Nonneg`, bundle value `valOf`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §5.2.1, eq. (22), p.25

import Mathlib
import Definitions.Def_TIEMaximin_Basic
import Definitions.Def_TIEMaximin_Deficient

namespace TIEMaximin

/-- **Equation (22)** (§5.2.1, p.25). For a deficient agent `i`, `Σ_{g∈L_i} f_g = n(a_i − 1) + (n −
1)(a_i − q_i)`.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, §5.2.1, eq. (22), p.25.

**Formalization Note.** Stated for every `α ∈ (0,1)`: the page's proof uses only Lemma 3.10, not
the hypothesis of Case 1 under which (22) is displayed, nor `α = 1/6`. -/
theorem eq_22 {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (v : Fin n → Fin m → ℝ) (hv : Nonneg v) (i : Fin n) (hi : IsDeficient α v i) :
    ((∑ g ∈ low α v i, nom v g : ℕ) : ℝ) =
      (n : ℝ) * ((aDef α v i : ℝ) - 1) + ((n : ℝ) - 1) * ((aDef α v i : ℝ) - qDef α v i) := by sorry

end TIEMaximin
