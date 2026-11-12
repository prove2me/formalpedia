-- Prove2me | Theorems.Thm_RiskBalancingMNL_lemma_1
-- name    : RiskBalancingMNL.lemma_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T12:43:29.660866+00:00
-- url     : https://prove2.me/theorems/0ebf8817-b562-4c3f-83d6-a73f66fe319e
-- title:
--   Lemma 1 — equal markup under symmetric price sensitivity, without an interior-solution hypothesis
-- statement:
--   Fix the MNL model with symmetric price sensitivity and a risk weight $\lambda\in[0,1)$.
--
--   1. For every feasible markup vector $m$ ($\pi(m)\ge0$) that is not an equal markup, there is an equal markup $t\ge0$ with
--   $$
--   L_\lambda(m)<L_\lambda(t,\dots,t).
--   $$
--   2. Consequently every optimal solution of problem (6) is an equal markup $(t,\dots,t)$: the equal-markup property holds.
--
--   The paper assumes that an interior solution exists; this statement needs no such assumption, since part 1 compares every feasible vector with an equal markup.
--
--   Differences from the source:
--   - generalization: "Assume an interior solution exists. Then the equal-markup property holds" → no existence hypothesis; every feasible non-equal markup vector is strictly beaten by an equal markup t ≥ 0, and every optimal vector is an equal markup; reason: part 2 is the printed lemma; part 1 implies it and is meaningful whether or not an optimum exists
--   - reading: "the equal-markup property holds" → every optimal solution of (6), for λ ∈ [0,1), has the same markup on every product; reason: the property is the equal markup across products at the optimum (p.10); λ ∈ [0,1) is the range of (5)
--   - encoding: problem (6) over shares q ≥ 0 with Σqᵢ ≤ 1 → over markup vectors m ∈ ℝⁿ with π(m) ≥ 0; reason: the paper's one-to-one map between m and q (p.9); shares with qᵢ = 0 have no markup
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), Lemma 1, p.10

import Mathlib
import Definitions.Def_RiskBalancingMNL_Params

namespace RiskBalancingMNL

/-- **Lemma 1 (Equal Markup under Symmetric Price Sensitivity)**, Li & Webster, *Optimizing
Risk-balancing Return under Discrete Choice Models*, SSRN 3959428 (PDF of 2021-11-14), p.10, in a
strengthened form without the hypothesis "Assume an interior solution exists". For every risk
weight `λ ∈ [0, 1)`:
1. every feasible markup vector that is not an equal markup is strictly beaten by some equal
   markup `t ≥ 0`;
2. consequently every optimal markup vector of (6) is an equal markup (the printed lemma). -/
theorem lemma_1 {n : ℕ} (P : Params n) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    (∀ m : Fin n → ℝ, Feasible P m → (¬ ∃ t : ℝ, m = constM t) →
      ∃ t : ℝ, 0 ≤ t ∧ objective P lam m < objective P lam (constM t)) ∧
    (∀ m : Fin n → ℝ, IsOptimal P lam m → ∃ t : ℝ, m = constM t) := by sorry

end RiskBalancingMNL
