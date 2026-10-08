-- Prove2me | Theorems.Thm_RiskControl_WSR_factor_nonneg
-- name    : RiskControl.WSR.factor_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:43.487278+00:00
-- url     : https://prove2.me/theorems/64d10272-f3be-47d3-b56f-8216d97ea157
-- title:
--   Proof of Proposition 5, p. 26 — νᵢ ∈ [0, 1] and each factor 1 − νⱼ(Lⱼ − R) is nonnegative
-- statement:
--   Let $n \in \mathbb N$ and $\delta \in \mathbb R$, and let $\nu_i$, $L_j$ be the betting fractions and losses of Proposition 5 (see the definition `RiskControl.WSR.Process`). Then:
--
--   1. for every sample $\omega \in \mathbb R^n$ and every index $i$, $0 \le \nu_i \le 1$;
--   2. for every sample with all losses $L_1, \dots, L_n \in [0,1]$, every $R \in [0,1]$ and every $1 \le j \le n$,
--   $$1 - \nu_j\,(L_j - R) \ge 0.$$
--
--   This is the step of the proof of Proposition 5 that makes the capital process $\mathcal K_i(R)$ nonnegative at the true mean $R = R(\lambda) \in [0,1]$, which Ville's inequality requires.
--
--   **Formalization Note** The losses lie in $[0,1]$ by the standing assumption of §3.1 of the paper (the loss is nonnegative and bounded by one); $R \in [0,1]$ because the true mean of $[0,1]$-valued losses lies there, which is the paper's "$(L_i(\lambda) - R(\lambda)) \in [-1,1]$". Part 1 holds for every $\delta$ and every $n$.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, Proof of Proposition 5, p. 26, sentence after the first display

import Mathlib
import Definitions.Def_RiskControl_WSR_Process

namespace RiskControl.WSR

/-- Proof of Proposition 5, p. 26 (arXiv:2101.02703v3): `ν_i ∈ [0, 1]` for every sample and
every index, and, for losses in `[0, 1]` and `R ∈ [0, 1]`, each factor
`1 − ν_j(λ)(L_j(λ) − R)` of the capital process is nonnegative. -/
theorem factor_nonneg (n : ℕ) (δ : ℝ) :
    (∀ (ω : Fin n → ℝ) (i : ℕ), 0 ≤ nu n δ ω i ∧ nu n δ ω i ≤ 1) ∧
    (∀ ω : Fin n → ℝ, (∀ j, ω j ∈ Set.Icc (0 : ℝ) 1) →
      ∀ R ∈ Set.Icc (0 : ℝ) 1, ∀ j : ℕ, 1 ≤ j → j ≤ n →
        0 ≤ 1 - nu n δ ω j * (obs ω j - R)) := by sorry

end RiskControl.WSR
