-- Prove2me | Theorems.Thm_RobustPCA_Recovery_theorem_2_3
-- name    : RobustPCA.Recovery.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:05.541367+00:00
-- url     : https://prove2.me/theorems/61d6a03b-5884-433c-98ca-9440124b6959
-- title:
--   Theorem 2.3 — derandomization: random signs on $\mathrm{Ber}(2\rho_s)$ dominate fixed signs on $\mathrm{Ber}(\rho_s)$
-- statement:
--   Let $\lambda\ge0$, $0\le\rho_s\le1/2$, and let $L_0,S\in\mathbb R^{n\times n}$ be fixed. Consider two models for the sparse component.
--
--   1. **Random signs.** $S_0=|S|\circ E$ (entrywise product), where $E$ has independent entries equal to $1$ and $-1$ with probability $\rho_s$ each and to $0$ with probability $1-2\rho_s$; that is, the support is $\mathrm{Ber}(2\rho_s)$ and the signs are i.i.d. symmetric and independent of the support.
--   2. **Fixed signs.** $S_0=\mathcal P_\Omega S$ with $\Omega\sim\mathrm{Ber}(\rho_s)$.
--
--   Then
--   $$\mathbb P_{\text{fixed}}\big(\text{PCP with input }L_0+S_0\text{ is exact}\big)\ \ge\ \mathbb P_{\text{random}}\big(\text{PCP with input }L_0+S_0\text{ is exact}\big),$$
--   where "exact" means that $(L_0,S_0)$ is the unique solution of (1.1) with weight $\lambda$.
--
--   So it suffices to prove the main theorem when the signs of the sparse component are random.
--
--   **Formalization Note** The paper states the theorem for $L_0$ obeying the conditions of Theorem 1.1 and a high-probability guarantee; its proof is a coupling that never uses either, so the inequality is stated for every $L_0$ and every probability level. The bound $\rho_s\le1/2$ makes $2\rho_s$ a probability.
-- source:
--   Candès, Li, Ma, Wright, Robust principal component analysis?, J. ACM 58(3) (2011), p. 11, Theorem 2.3 (proof pp. 11–12)

import Definitions.Def_RobustPCA_Recovery_Setup
open MatrixCompletion

namespace RobustPCA.Recovery

/-- Theorem 2.3 (derandomization), p. 11: for every fixed `S`, the probability that PCP
recovers `(L0, |S| ∘ E)` with random signs `E` (support `∼ Ber(2ρs)`, i.i.d. symmetric signs)
is at most the probability that PCP recovers `(L0, 𝒫_Ω S)` with fixed signs and `Ω ∼ Ber(ρs)`. -/
theorem theorem_2_3 {n : ℕ} (lam ρs : ℝ) (L0 S : RealMatrix n n) (hlam : 0 ≤ lam)
    (hρ0 : 0 ≤ ρs) (hρ1 : ρs ≤ 1 / 2) :
    randomSignProb (2 * ρs) (fun E => IsPCPExact lam L0 (fun i j => |S i j| * E i j)) ≤
      bernoulliEventProb ρs (fun Ω => IsPCPExact lam L0 (samplingProjection Ω S)) := by sorry

end RobustPCA.Recovery
