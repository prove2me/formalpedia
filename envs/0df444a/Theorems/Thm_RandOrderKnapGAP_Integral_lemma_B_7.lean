-- Prove2me | Theorems.Thm_RandOrderKnapGAP_Integral_lemma_B_7
-- name    : RandOrderKnapGAP.Integral.lemma_B_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:27:03.209509+00:00
-- url     : https://prove2.me/theorems/08b31b0a-e2ec-4431-8922-39dd5852276f
-- title:
--   Lemma B.7 — sizes in $[0,\delta]$ with sum $C$ have sum of squares at most $J(C)$, attained
-- statement:
--   Let $\delta>0$. If finitely many sizes satisfy $0\le a_r\le\delta$ and $\sum_r a_r=C$, then
--   $$\sum_r a_r^2\le J(C)=m\delta^2+(C-m\delta)^2,\qquad m=\lfloor C/\delta\rfloor .$$
--   The bound is attained by taking $m$ sizes equal to $\delta$, at most one additional size equal to $C-m\delta$, and all remaining sizes equal to zero.
--
--   The lemma bounds the second moment of the observed small-item mass in the analysis of the rule family (§B.7.2) and in (B.51).
--
--   Differences from the source:
--   - generalization: δ = 1/3 (fixed from §B.4 on) → any δ > 0; reason: the statement holds for every positive δ; δ = 1/3 is the instance used by the paper
--   - encoding: finitely many sizes a_r → a : Fin r → ℝ for some r : ℕ; reason: Lean convention
--   - reading: the bound is attained by m sizes δ, at most one size C − mδ and zeros → for C ≥ 0 and r ≥ m slots (r ≥ m + 1 when C ≠ mδ), the family δ,…,δ, C − mδ, 0,… satisfies the constraints, has sum C and sum of squares J(C); reason: attainment needs enough sizes to hold the configuration; C ≥ 0 is forced by the constraints
-- source:
--   Agrawal, Khan, Pareek, Improved Algorithms in the Random-Order Model: Knapsack, GAP, and Beyond, STOC 2027 submission (manuscript sha256 7825a05f…), p. 50 (PDF 52), Lemma B.7

import Mathlib
import Definitions.Def_RandOrderKnapGAP_Integral_Constants

open scoped BigOperators

namespace RandOrderKnapGAP.Integral

/-- **Lemma B.7** (largest sum of squared sizes), p. 50. Let `δ > 0`. If finitely many sizes
satisfy `0 ≤ a_r ≤ δ` and `∑ a_r = C`, then `∑ a_r² ≤ J(C) = m δ² + (C − m δ)²`,
`m = ⌊C/δ⌋`. The bound is attained: for `C ≥ 0` and any number of slots that can hold the
configuration, `m` sizes equal to `δ`, one size `C − m δ` (when it is nonzero, it needs a slot)
and all others `0` satisfy the constraints and have sum of squares exactly `J(C)`. -/
theorem lemma_B_7 (δ : ℝ) (hδ : 0 < δ) :
    (∀ (r : ℕ) (a : Fin r → ℝ) (C : ℝ), (∀ j, 0 ≤ a j ∧ a j ≤ δ) → ∑ j, a j = C →
      ∑ j, a j ^ 2 ≤ Jbound δ C) ∧
    (∀ (C : ℝ), 0 ≤ C → ∀ r : ℕ, ⌊C / δ⌋₊ ≤ r → (C ≠ (⌊C / δ⌋₊ : ℝ) * δ → ⌊C / δ⌋₊ + 1 ≤ r) →
      let a : Fin r → ℝ := fun j =>
        if j.val < ⌊C / δ⌋₊ then δ
        else if j.val = ⌊C / δ⌋₊ then C - (⌊C / δ⌋₊ : ℝ) * δ else 0
      (∀ j, 0 ≤ a j ∧ a j ≤ δ) ∧ ∑ j, a j = C ∧ ∑ j, a j ^ 2 = Jbound δ C) := by sorry

end RandOrderKnapGAP.Integral
