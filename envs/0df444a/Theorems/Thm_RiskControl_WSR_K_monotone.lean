-- Prove2me | Theorems.Thm_RiskControl_WSR_K_monotone
-- name    : RiskControl.WSR.K_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:41.65377+00:00
-- url     : https://prove2.me/theorems/10c8cecf-0c22-4c29-a338-a82f8135693f
-- title:
--   Proof of Proposition 5, p. 26 — for losses in [0, 1], each 𝒦ᵢ(R) is nondecreasing in R on R ≥ 0
-- statement:
--   Let $n \in \mathbb N$, $\delta \in \mathbb R$, and let $\omega = (L_1, \dots, L_n)$ be a sample with every $L_j \in [0,1]$. Then for every index $i$ the capital $\mathcal K_i(R)$ of Proposition 5 (see the definition `RiskControl.WSR.Process`) is a nondecreasing function of $R$ on $[0, \infty)$:
--   $$0 \le R \le R' \implies \mathcal K_i(R) \le \mathcal K_i(R').$$
--
--   This monotonicity is what turns the bound at a single value of $R$ (the true mean) into a statement about the infimum $\widehat R^+_{\mathrm{WSR}}$.
--
--   **Formalization Note** The paper says "increasing in $R$ almost surely"; the statement is the nondecreasing version (for $i = 0$, or when $\nu_j = 0$, $\mathcal K_i$ is constant in $R$), and "almost surely" is the condition that the observed losses lie in $[0,1]$. The range $R \ge 0$ is the range of the infimum defining $\widehat R^+_{\mathrm{WSR}}$; there every factor $1 - \nu_j(L_j - R)$ is nonnegative because $L_j \le 1$ and $\nu_j \le 1$.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, Proof of Proposition 5, p. 26, sentence after the second display

import Mathlib
import Definitions.Def_RiskControl_WSR_Process

namespace RiskControl.WSR

/-- Proof of Proposition 5, p. 26 (arXiv:2101.02703v3): for a sample of losses in `[0, 1]`,
every `𝒦_i(R; λ)` is nondecreasing in `R` on `R ≥ 0`. -/
theorem K_monotone (n : ℕ) (δ : ℝ) (ω : Fin n → ℝ) (hω : ∀ j, ω j ∈ Set.Icc (0 : ℝ) 1)
    (i : ℕ) :
    MonotoneOn (fun R => K n δ ω i R) (Set.Ici 0) := by sorry

end RiskControl.WSR
