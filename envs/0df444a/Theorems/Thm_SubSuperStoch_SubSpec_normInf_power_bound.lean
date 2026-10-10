-- Prove2me | Theorems.Thm_SubSuperStoch_SubSpec_normInf_power_bound
-- name    : SubSuperStoch.SubSpec.normInf_power_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:38.647631+00:00
-- url     : https://prove2.me/theorems/29020ef8-d81b-49d1-8ca8-3cb169b7d89c
-- title:
--   Proof of Theorem 2.2, p. 5 — ‖F^{|C*|+1}‖_∞ ≤ 1 − (1 − α₁)α₂^{|C*|} < 1
-- statement:
--   Under the hypotheses of Theorem 2.2 — $F$ an $n\times n$ sub-stochastic matrix with $\mathcal S_1=\{s\mid\Lambda_s[F]<1\}$ and $\mathcal S_2=\{s\mid\Lambda_s[F]=1\}$ non-empty, a non-zero element chain $\mathcal C_{i\to k}$ from some $i\in\mathcal S_1$ given for each $k\in\mathcal S_2$, and $\alpha_1,\alpha_2,|\mathcal C^*|$ as defined there — the infinite norm of the power $F^{|\mathcal C^*|+1}$ satisfies
--   $$\big\|F^{|\mathcal C^*|+1}\big\|_\infty\le 1-(1-\alpha_1)\alpha_2^{|\mathcal C^*|}<1 .$$
--
--   This collects the row bounds for $\mathcal S_1$ and $\mathcal S_2$ into one norm bound, which is then turned into the spectral bound (2.1).
--
--   **Formalization Note** `normInf` is the largest absolute row sum; since $F^{|\mathcal C^*|+1}$ is nonnegative it equals the largest row sum. The chain data are passed exactly as in the goal theorem.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 5, proof of Theorem 2.2 (display ‖F^{|C*|+1}‖_∞ ≤ 1 − (1 − α₁)α₂^{|C*|} < 1)

import Mathlib
import Definitions.Def_SubSuperStoch_SubSpec_Setting

namespace SubSuperStoch.SubSpec

theorem normInf_power_bound {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsSubStochastic F)
    (hS₁ : ∃ s, rowSum F s < 1) (hS₂ : ∃ s, rowSum F s = 1)
    (len : Fin n → ℕ)
    (hchain : ∀ k, rowSum F k = 1 → ∃ i, rowSum F i < 1 ∧
      ∃ c : ℕ → Fin n, c 0 = i ∧ c (len k) = k ∧ 1 ≤ len k ∧ IsChain F c (len k))
    (α₁ : ℝ) (hα₁ : IsGreatest {x | ∃ s, rowSum F s < 1 ∧ x = rowSum F s} α₁)
    (α₂ : ℝ) (hα₂ : IsLeast {x | ∃ i j, 0 < F i j ∧ x = F i j} α₂)
    (C : ℕ) (hC : IsGreatest {m | ∃ k, rowSum F k = 1 ∧ m = len k} C) :
    normInf (F ^ (C + 1)) ≤ 1 - (1 - α₁) * α₂ ^ C ∧ 1 - (1 - α₁) * α₂ ^ C < 1 := by sorry

end SubSuperStoch.SubSpec
