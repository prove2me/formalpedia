-- Prove2me | Theorems.Thm_RiskBalancingMNL_Supplement_theorem_3
-- name    : RiskBalancingMNL.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:58:30.684804+00:00
-- url     : https://prove2.me/theorems/3a0fdfb4-8245-4b12-a2d0-a7fbebdeacbd
-- title:
--   Theorem 3 — $m^*_1\le\dots\le m^*_n$ and $\check m^*_1\ge\dots\ge\check m^*_n$ when $\hat b_1\ge\dots\ge\hat b_n$
-- statement:
--   Consider the MNL model with asymmetric price sensitivities, with products indexed so that $\hat b_1\ge\hat b_2\ge\dots\ge\hat b_n>0$, and a risk weight $\lambda\in(0,1)$. Let $m^*$ be an optimal markup vector of problem (6) that satisfies Assumption 1, $\lambda\le\pi^*/m^*_{\max}$. Then
--   $$
--   m^*_1\le m^*_2\le\dots\le m^*_n\qquad\text{and}\qquad \check m^*_1\ge\check m^*_2\ge\dots\ge\check m^*_n,
--   $$
--   where $\check m^*_j=m^*_j-1/\hat b_j$ is the adjusted markup. Products that are less price sensitive carry higher markups but lower adjusted markups: under risk balancing the equal-adjusted-markup rule of profit maximization is replaced by an ordering.
--
--   **Formalization Note** The indexing is the hypothesis that $\hat b$ is antitone in the index. Assumption 1 is written $\lambda m_i\le\pi$ for every $i$.
--
--   Differences from the source:
--   - generalization: Assumption 1: λ ≤ π*/m*_max at the optimum → λ · m_i ≤ π(m) for every i; reason: equivalent when m*_max > 0; at m = 0, where the printed quotient is undefined, the Lean hypothesis holds and (19) holds (θ = 0)
--   - encoding: products indexed so that b̂_1 ≥ b̂_2 ≥ … ≥ b̂_n (p.14); m*_1 ≤ … ≤ m*_n; m̌*_1 ≥ … ≥ m̌*_n → hypothesis Antitone b̂ on Fin n; Monotone m and Antitone (m_j − 1/b̂_j); reason: a chain inequality over consecutive indices is monotonicity in the index
--   - reading: λ ∈ [0, 1) (problem (5)) → 0 < λ < 1; reason: θ contains π/λ, undefined at λ = 0
--   - encoding: problem (6) over share vectors q → IsOptimal over all markup vectors m ∈ ℝⁿ with π(m) ≥ 0; reason: the paper's one-to-one map between markups and shares (p.9), as in the published base mission
--   - encoding: primitives a_i, y_i, b, β of (16) → reduced form â_i, b̂_i > 0, c_i; reason: the primitives enter only through â_i = a_i + y_i and b̂_i = b − βy_i, and every positive b̂ arises
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), §5.1, Theorem 3, p.16; ordering of $\hat b$, p.14; Assumption 1, p.15

import Mathlib
import Definitions.Def_RiskBalancingMNL_Supplement_AsymParams

namespace RiskBalancingMNL.Supplement

/-- **Theorem 3 (Sequence of Markups and Adjusted Markups)**, Li & Webster, *Optimizing
Risk-balancing Return under Discrete Choice Models*, SSRN 3959428 (PDF of 2021-11-14), p.16: with
products indexed so that `b̂₁ ≥ b̂₂ ≥ … ≥ b̂ₙ` (p.14), the optimal markups satisfy
`m*₁ ≤ … ≤ m*ₙ` and the optimal adjusted markups `m̌*ⱼ = m*ⱼ − 1/b̂ⱼ` satisfy `m̌*₁ ≥ … ≥ m̌*ₙ`.

Stated for `λ ∈ (0, 1)` and every optimal markup vector `m` that satisfies Assumption 1.

**Formalization Note** The indexing convention of p.14 is the hypothesis `Antitone P.bHat`.
Assumption 1 is encoded as in `theorem_2`. -/
theorem theorem_3 {n : ℕ} (P : AsymParams n) (hord : Antitone P.bHat) (lam : ℝ)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (m : Fin n → ℝ) (hm : P.IsOptimal lam m)
    (hA1 : ∀ i, lam * m i ≤ P.profit m) :
    Monotone m ∧ Antitone (P.adjMarkup m) := by sorry

end RiskBalancingMNL.Supplement
