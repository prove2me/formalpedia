-- Prove2me | Theorems.Thm_RiskUncSets_Distortion_theorem_4_3
-- name    : RiskUncSets.Distortion.theorem_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:29:12.558655+00:00
-- url     : https://prove2.me/theorems/2db1bcef-19a2-437d-b5da-6ffe7dcc165d
-- title:
--   Theorem 4.3, p. 1490 — for a distortion risk measure μ_q, μ(ã′x − b) ≤ 0 iff a′x ≥ b on the q-permutohull iff an explicit linear system in (y₁, y₂) is feasible
-- statement:
--   Let $\Omega = \{\omega_1, \dots, \omega_N\}$, $N \ge 1$, carry the uniform distribution (Assumption 4.1), and let $\mu$ be a distortion risk measure: coherent, comonotonic and law invariant. Then there is $q \in \hat\Delta^N$ with $\mu(X) = -\sum_{i=1}^N q_i x_{(i)}$ for all $X$ (Theorem 4.2), and for this $q$, for all data $a_1, \dots, a_N \in \mathbb R^n$ (any $n$) and every $b \in \mathbb R$,
--   $$\begin{aligned}
--   \{x \in \mathbb R^n : \mu(\tilde a'x - b) \le 0\}
--   &= \{x \in \mathbb R^n : a'x \ge b \ \ \forall a \in \Pi_q(\mathcal A)\} \\
--   &= \{x \in \mathbb R^n : \exists (y_1, y_2) \in \mathbb R^N \times \mathbb R^N,\ e'y_1 + e'y_2 \ge b,\ y_{1,i} + y_{2,j} \le q_i\,(a_j'x)\ \forall (i,j) \in \{1,\dots,N\}^2\}.
--   \end{aligned}$$
--   Here $\tilde a$ takes the value $a_i$ at $\omega_i$, $\tilde a'x - b$ is the random variable $\omega_i \mapsto a_i'x - b$, and $\Pi_q(\mathcal A)$ is the $q$-permutohull of $\mathcal A = \{a_1, \dots, a_N\}$.
--
--   The theorem says that a risk constraint under any distortion risk measure is a robust linear constraint whose uncertainty set is a permutohull of the data, and that this robust constraint has a polynomial-size linear reformulation.
--
--   **Formalization Note** The page prints $\{x : \mu(\tilde a'x - b) \ge 0\}$. The risk-aversion constraint of the paper is $\mu(\tilde a'x - b) \le 0$ (p. 1486), and the first equality follows from Theorem 3.1, whose proof gives $\mu(\tilde a'x - b) = -\inf_{a \in \mathcal U} a'x + b$; with $\ge 0$ the equality is false. The statement uses $\le 0$. The theorem uses $q$ without introducing it; it is the vector that Theorem 4.2 attaches to $\mu$, so the statement asserts the existence of $q \in \hat\Delta^N$ representing $\mu$ as in (4) before quantifying over the data: $q$ depends on $\mu$ only. Indices are 0-based and order statistics are `X ∘ Tuple.sort X`.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1490, Theorem 4.3; Theorem 4.2 and Definition 4.6, p. 1489; Definition 4.7, p. 1490; risk aversion constraint, p. 1486

import Mathlib
import Definitions.Def_RiskUncSets_Distortion_Setting

namespace RiskUncSets.Distortion

theorem theorem_4_3 {N : ℕ} (hN : 0 < N) (μ : (Fin N → ℝ) → ℝ)
    (hμ : IsDistortion (uniform N) μ) :
    ∃ q ∈ restrictedSimplex N, (∀ X, μ X = muQ q X) ∧
      ∀ (n : ℕ) (a : Fin N → Fin n → ℝ) (b : ℝ),
        {x : Fin n → ℝ | μ (fun i => a i ⬝ᵥ x - b) ≤ 0} =
            {x | ∀ a' ∈ permutohull q a, b ≤ a' ⬝ᵥ x} ∧
          {x : Fin n → ℝ | ∀ a' ∈ permutohull q a, b ≤ a' ⬝ᵥ x} =
            {x | ∃ y₁ y₂ : Fin N → ℝ, b ≤ ∑ i, y₁ i + ∑ j, y₂ j ∧
              ∀ i j, y₁ i + y₂ j ≤ q i * (a j ⬝ᵥ x)} := by sorry

end RiskUncSets.Distortion
