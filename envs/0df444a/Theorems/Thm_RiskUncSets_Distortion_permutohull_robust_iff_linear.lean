-- Prove2me | Theorems.Thm_RiskUncSets_Distortion_permutohull_robust_iff_linear
-- name    : RiskUncSets.Distortion.permutohull_robust_iff_linear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:29:13.031518+00:00
-- url     : https://prove2.me/theorems/64f7359d-dbc3-4384-a5f0-bc9d49585a90
-- title:
--   Proof of Theorem 4.3 via (6)–(7), p. 1490 — a′x ≥ b on Π_q(𝒜) iff ∃ y₁, y₂ with e′y₁ + e′y₂ ≥ b, y₁ᵢ + y₂ⱼ ≤ qᵢ a′ⱼx
-- statement:
--   Let $q \in \mathbb R^N$, let $a_1, \dots, a_N \in \mathbb R^n$ and $b \in \mathbb R$, and let $\Pi_q(\mathcal A) = \operatorname{conv}\{\sum_i q_{\sigma(i)} a_i : \sigma \in S_N\}$ be the $q$-permutohull of $\mathcal A = \{a_1, \dots, a_N\}$. For every $x \in \mathbb R^n$,
--   $$a'x \ge b \ \ \forall a \in \Pi_q(\mathcal A) \iff \exists (y_1, y_2) \in \mathbb R^N \times \mathbb R^N:\ e'y_1 + e'y_2 \ge b,\ \ y_{1,i} + y_{2,j} \le q_i\,(a_j'x)\ \ \forall (i,j) \in \{1, \dots, N\}^2.$$
--
--   This is the second equality of Theorem 4.3: the robust constraint over the permutohull, which has up to $N!$ extreme points, is equivalent to a linear system with $2N$ extra variables and $N^2$ constraints. In the paper it comes from writing $\min_{a \in \Pi_q(\mathcal A)} x'a$ as an assignment linear program (6) and passing to its dual (7).
--
--   **Formalization Note** The statement holds for every $q \in \mathbb R^N$; the paper states it for $q \in \hat\Delta^N$, and its argument does not use that restriction, so this is a generalization. In (6) the row and column constraints read "$i, j \in \{1, \dots, n\}$"; they range over $\{1, \dots, N\}$. For $N = 0$ both sides reduce to $b \le 0$. $e'y$ is `∑ i, y i`; indices are 0-based.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1490, Theorem 4.3 (second equality) and its proof, displays (6), (7); Definition 4.7, p. 1490

import Mathlib
import Definitions.Def_RiskUncSets_Distortion_Setting

namespace RiskUncSets.Distortion

theorem permutohull_robust_iff_linear {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) (b : ℝ)
    (x : Fin n → ℝ) :
    (∀ a' ∈ permutohull q a, b ≤ a' ⬝ᵥ x) ↔
      ∃ y₁ y₂ : Fin N → ℝ, b ≤ ∑ i, y₁ i + ∑ j, y₂ j ∧
        ∀ i j, y₁ i + y₂ j ≤ q i * (a j ⬝ᵥ x) := by sorry

end RiskUncSets.Distortion
