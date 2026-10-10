-- Prove2me | Theorems.Thm_SubSuperStoch_SubSpec_unit_rows_power_bound
-- name    : SubSuperStoch.SubSpec.unit_rows_power_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:24.895647+00:00
-- url     : https://prove2.me/theorems/7f05a52c-a55e-4a6e-98a6-c05c1721a7f8
-- title:
--   Proof of Theorem 2.2, p. 5 — Λ_k[F^{|C*|+1}] ≤ 1 − (1 − α₁)α₂^{|C*|} < 1 for every unit row k ∈ S₂
-- statement:
--   Let $F$ be an $n\times n$ sub-stochastic matrix with $\mathcal S_1=\{s\mid\Lambda_s[F]<1\}$ and $\mathcal S_2=\{s\mid \Lambda_s[F]=1\}$ non-empty. Suppose that for each $k\in\mathcal S_2$ a non-zero element chain $\mathcal C_{i\to k}$ starting at some $i\in\mathcal S_1$ is given, and let
--   $$|\mathcal C^*|=\max\{|\mathcal C_{i\to k}|\mid i\in\mathcal S_1,\ k\in\mathcal S_2\}$$
--   be the largest number of elements among these chains. With $\alpha_1$ and $\alpha_2$ as in Theorem 2.2, every $k\in\mathcal S_2$ satisfies
--   $$\Lambda_k\big[F^{|\mathcal C^*|+1}\big]\le 1-(1-\alpha_1)\alpha_2^{|\mathcal C^*|}<1 .$$
--
--   This is the step of the proof of Theorem 2.2 that passes from the bound at the end of each chain to a single power of $F$ common to all rows of sum one.
--
--   **Formalization Note** The chosen chain for $k$ has length `len k` (one chain per $k\in\mathcal S_2$, as the hypothesis of Theorem 2.2 provides), and $|\mathcal C^*|$ is `C` with `IsGreatest {m | ∃ k, rowSum F k = 1 ∧ m = len k} C`.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 5, proof of Theorem 2.2 (display Λ_k[F^{|C*|+1}] after "According to the definition of |C*|")

import Mathlib
import Definitions.Def_SubSuperStoch_SubSpec_Setting

namespace SubSuperStoch.SubSpec

theorem unit_rows_power_bound {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsSubStochastic F)
    (hS₁ : ∃ s, rowSum F s < 1) (hS₂ : ∃ s, rowSum F s = 1)
    (len : Fin n → ℕ)
    (hchain : ∀ k, rowSum F k = 1 → ∃ i, rowSum F i < 1 ∧
      ∃ c : ℕ → Fin n, c 0 = i ∧ c (len k) = k ∧ 1 ≤ len k ∧ IsChain F c (len k))
    (α₁ : ℝ) (hα₁ : IsGreatest {x | ∃ s, rowSum F s < 1 ∧ x = rowSum F s} α₁)
    (α₂ : ℝ) (hα₂ : IsLeast {x | ∃ i j, 0 < F i j ∧ x = F i j} α₂)
    (C : ℕ) (hC : IsGreatest {m | ∃ k, rowSum F k = 1 ∧ m = len k} C) :
    ∀ k, rowSum F k = 1 →
      rowSum (F ^ (C + 1)) k ≤ 1 - (1 - α₁) * α₂ ^ C ∧ 1 - (1 - α₁) * α₂ ^ C < 1 := by sorry

end SubSuperStoch.SubSpec
