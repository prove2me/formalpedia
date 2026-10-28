-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_theorem_5_5_equilibrium_condition
-- name    : SmoothAmbEq.Gaussian.theorem_5_5_equilibrium_condition
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-24T20:43:08.856955+00:00
-- url     : https://prove2.me/theorems/46e90553-386f-424a-8c7f-b22de02a9ecd
-- title:
--   Theorem 5.5, p. 19 — equilibrium inequality of Definition 2.1 for π* (finite J, limsup of spike quotients ≤ 0)
-- statement:
--   Consider the Gaussian-prior model of §5, with CARA utility $U(x)=-\frac1ke^{-kx}$ and ambiguity function $\phi(u)=-\frac1\alpha(-u)^\alpha$ ($\alpha\ne0$), $\phi(u)=-\log(-u)$ ($\alpha=0$). Assume $\alpha>\max\{\alpha^*,1-0.5\sigma_0^{-2}\sigma^2T^{-1}\}$, let $(m_1,\dots,m_6)$ solve (5.10) on $[0,T]$, and let $\pi^*$ be the strategy (5.12).
--
--   For a strategy $\pi$, write
--   $$J(t,x,\beta,\pi)=\mathbb E\big[\phi\big(g^{Z,\pi}(t,x,\beta)\big)\mid\beta_t=\beta\big],\qquad g^{z,\pi}(t,x,\beta)=\mathbb E\big[U(X^{z,\pi}_T)\mid X^{z,\pi}_t=x,\ \beta^z_t=\beta\big],$$
--   where $Z\mid\beta_t=\beta\sim N(\beta,\zeta(t))$. Let $\pi_{t,h}$ be the spike variation equal to $\pi$ on $[t,t+h)$ and to $\pi^*$ elsewhere. Then for every $(t,x,\beta)\in[0,T)\times\mathbb R^2$:
--
--   1. $J(t,x,\beta,\pi^*)$ is finite: $U(X^{z,\pi^*}_T)$ is integrable for every $z$, and $z\mapsto\phi(g^{z,\pi^*}(t,x,\beta))$ is integrable under $N(\beta,\zeta(t))$;
--   2. for every admissible $\pi\in\Pi$ whose spike variations $\pi_{t,h}$ are admissible for all small $h>0$, the value $J(t,x,\beta,\pi_{t,h})$ is finite for all small $h>0$, and
--   $$\limsup_{h\to0^+}\frac{J(t,x,\beta,\pi_{t,h})-J(t,x,\beta,\pi^*)}{h}\le0 .$$
--
--   Together with the admissibility of $\pi^*$, this is the first assertion of Theorem 5.5: $\pi^*$ is an equilibrium strategy in the sense of Definition 2.1. In the paper it is the conclusion of the verification Theorem 4.5. Its conditions are (a) from Lemma 5.3 and Proposition 5.4, (b) from Step 1, and (c) from Steps 2–6 of Appendix G.
--
--   **Formalization Note** This is the second conjunct of the predicate `IsEquilibrium` of the mission's Equilibrium definition. The first conjunct, $\pi^*\in\Pi$, is the milestone `pi_star_admissible`. The $\limsup$ is written in $\varepsilon$-form, and finiteness of $J$ is stated explicitly, exactly as in `IsEquilibrium`. The hypotheses are those of Theorem 5.5.
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, p. 19, Theorem 5.5 (first assertion), with Definition 2.1 (p. 7) and Appendix G (pp. 39–43)

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
import Definitions.Def_SmoothAmbEq_Gaussian_Equilibrium
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace SmoothAmbEq.Gaussian

/-- Theorem 5.5, p. 19, first assertion, equilibrium inequality (the part of Definition 2.1
beyond `π* ∈ Π`, which is `pi_star_admissible`). Under the hypotheses of Theorem 5.5, for every
`(t, x, β) ∈ [0, T) × ℝ²`, `J(t, x, β, π*)` is finite, and for every `π ∈ Π` whose spike
variations `π_{t,h}` are admissible for small `h > 0`, `J(t, x, β, π_{t,h})` is finite for small
`h` and `limsup_{h → 0+} [J(t, x, β, π_{t,h}) - J(t, x, β, π*)] / h ≤ 0` (in `ε`-form). -/
theorem theorem_5_5_equilibrium_condition (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : max a (1 - 1 / 2 * (M.σ ^ 2 / (M.σ₀ ^ 2 * M.T))) < M.α) (c : Coeffs)
    (hc : SolvesODE510 M c) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) :
    ∀ t ∈ Ico 0 M.T, ∀ x β : ℝ,
      HasFiniteJ M P W (piStar M c) t x β ∧
      ∀ π : Strategy, Admissible M P W π →
        (∀ᶠ h in 𝓝[>] (0 : ℝ), Admissible M P W (spike π (piStar M c) t h)) →
        (∀ᶠ h in 𝓝[>] (0 : ℝ), HasFiniteJ M P W (spike π (piStar M c) t h) t x β) ∧
        ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝[>] (0 : ℝ),
          (J M P W (spike π (piStar M c) t h) t x β - J M P W (piStar M c) t x β) / h ≤ ε := by
  sorry

end SmoothAmbEq.Gaussian
