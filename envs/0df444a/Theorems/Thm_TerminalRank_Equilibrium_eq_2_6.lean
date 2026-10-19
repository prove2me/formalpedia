-- Prove2me | Theorems.Thm_TerminalRank_Equilibrium_eq_2_6
-- name    : TerminalRank.Equilibrium.eq_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:04.38899+00:00
-- url     : https://prove2.me/theorems/6af0e71a-bd28-4b92-b8ff-368422701463
-- title:
--   (2.6), p. 5, for R ∈ ℛ_b — the path-space value equals a static entropic problem over terminal laws
-- statement:
--   Let $T>0$, $c>0$, $\sigma>0$, $x_0\in\mathbb R$, let $B$ be a Brownian motion under the probability measure $P$, $X_T=x_0+\sigma B_T$, and let $P_T$ be the law of $X_T$ under $P$. For every bounded reward $R\in\mathcal R_b$ and every population law $\tilde\mu\in\mathcal P(\mathbb R)$ with a finite first moment,
--   $$V(R,\tilde\mu)=\sup_{\mu\in\mathcal P(\mathbb R):\ \mu\sim P_T}\ \int_{\mathbb R}R_{\tilde\mu}(x)\,d\mu(x)-2c\sigma^2H\big(\mu\,|\,\mathcal N(x_0,\sigma^2T)\big).$$
--
--   This is the Schrödinger-bridge reduction: the optimization over path measures $Q$ in (2.3) splits into a choice of terminal law $\mu$ and an entropy minimization over bridges, whose minimum is the entropy of $\mu$ relative to the Gaussian terminal law. It turns the control problem into a static calculus-of-variations problem.
--
--   **Formalization Note.** The paper derives (2.6) for every $R\in\mathcal R$; it is stated here for bounded rewards, where the expectation in (2.3) is defined. The finite-mean condition on $\tilde\mu$ makes the paper's $R_{\tilde\mu}$ defined. The supremum runs over $\mu\sim P_T$ with $H(\mu|\mathcal N(x_0,\sigma^2T))<\infty$; the remaining $\mu$ have value $-\infty$. $P_T$ is kept as the push-forward of $P$ under $X_T$, as printed.
-- source:
--   Bayraktar & Zhang, Terminal Ranking Games, arXiv:1906.09628v2, p. 5, (2.6)

import Mathlib
import Definitions.Def_TerminalRank_Equilibrium_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TerminalRank.Equilibrium

/-- (2.6), p. 5 (Bayraktar–Zhang, arXiv:1906.09628v2), specialized to bounded rewards `R ∈ ℛ_b`:
the path-space value (2.3) equals the static problem over terminal laws `µ ∼ P_T`,
`V(R, µ̃) = sup_{µ ∼ P_T} ∫ R_µ̃ dµ − 2cσ² H(µ | 𝒩(x0, σ²T))`, where `P_T` is the law of `X_T`
under `P`. The population law `µ̃` has a finite mean so that `R_µ̃` is defined. The supremum
is over `µ` with finite entropy (the others have value `−∞`). -/
theorem eq_2_6 {Ω : Type*} [MeasurableSpace Ω] (x0 σ c : ℝ) (T : ℝ≥0)
    (hσ : 0 < σ) (hc : 0 < c) (hT : 0 < T)
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (R : ℝ → ℝ → ℝ → ℝ) (hR : IsBddReward R) (μt : Measure ℝ) [IsProbabilityMeasure μt]
    (hμt : Integrable (fun y : ℝ => y) μt) :
    V x0 σ c T P B R μt =
      sSup {v : ℝ | ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ ≪ P.map (XT x0 σ B T) ∧
        P.map (XT x0 σ B T) ≪ μ ∧ InformationTheory.klDiv μ (normalLaw x0 σ T) ≠ ⊤ ∧
        v = ∫ x, Rmu R μt x ∂μ - 2 * c * σ ^ 2 * (InformationTheory.klDiv μ (normalLaw x0 σ T)).toReal} := by sorry

end TerminalRank.Equilibrium
