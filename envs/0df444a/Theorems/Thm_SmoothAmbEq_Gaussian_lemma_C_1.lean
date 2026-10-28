-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_lemma_C_1
-- name    : SmoothAmbEq.Gaussian.lemma_C_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:07.408733+00:00
-- url     : https://prove2.me/theorems/f194bd91-7bed-46a7-9a3f-65fdecf291a8
-- title:
--   Lemma C.1, p. 25 — short-horizon exponential moments of β^z, uniform in (t, β, z): (C.3) and (C.4)
-- statement:
--   Let $\beta^z$ be the posterior-mean process (C.1) started at $\beta^z_t=\beta$. For any $C>0$ and $\epsilon>0$ there exists $h>0$ such that, for all $t\in[0,T)$, $\beta\in\mathbb R$ and $z\in\mathbb R$,
--   $$\mathbb E\Big[\exp\Big\{C\int_t^{(t+h)\wedge T}(\beta^z_u)^2du\Big\}\ \Big|\ \beta^z_t=\beta\Big]\le\frac43e^{\epsilon(z^2+\beta^2)}\qquad\text{(C.3)}$$
--   and
--   $$\sup_{s\in[t,(t+h)\wedge T)}\mathbb E\big[\exp\{C(\beta^z_s)^2\}\mid\beta^z_t=\beta\big]\le\sqrt2\,e^{\epsilon z^2+3C\sigma_0^4\zeta(T)^{-2}\beta^2}.\qquad\text{(C.4)}$$
--
--   The bounds are uniform in the unobserved drift $z$ up to the factor $e^{\epsilon z^2}$, which is what makes the Gaussian averaging over $z$ in $J$ possible.
--
--   **Formalization Note** "Given $\beta^z_t=\beta$" is the process (C.1) started at $(t,\beta)$ and driven by $W_s-W_t$. The step $h$ depends only on $C$, $\epsilon$ and the model: it is chosen before the probability space, $t$, $\beta$ and $z$. Expectations are lower Lebesgue integrals of nonnegative quantities.
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, p. 25, Lemma C.1, (C.3)–(C.4)

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SmoothAmbEq.Gaussian

/-- Lemma C.1, p. 25. For any `C > 0` and `ε > 0` there is `h > 0` (depending only on `C`, `ε`
and the model) such that for every probability space carrying a Brownian motion `W`, every
`t ∈ [0, T)`, `β ∈ ℝ` and `z ∈ ℝ`, the process `β^z` of (C.1) started at `β^z_t = β` satisfies
(C.3) `E[exp{C ∫_t^{(t+h)∧T} (β^z_u)² du}] ≤ (4/3) e^{ε(z²+β²)}` and
(C.4) `sup_{s ∈ [t,(t+h)∧T)} E[exp{C (β^z_s)²}] ≤ √2 e^{εz² + 3Cσ₀⁴ζ(T)⁻²β²}`. -/
theorem lemma_C_1 (M : Model) :
    ∀ C > (0 : ℝ), ∀ ε > (0 : ℝ), ∃ h > (0 : ℝ),
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : ℝ≥0 → Ω → ℝ), IsBrownianReal W P →
      ∀ t ∈ Ico 0 M.T, ∀ β z : ℝ,
        (∫⁻ ω, ENNReal.ofReal
            (Real.exp (C * ∫ u in t..min (t + h) M.T, (betaZ M W z t β u ω) ^ 2)) ∂P)
          ≤ ENNReal.ofReal (4 / 3 * Real.exp (ε * (z ^ 2 + β ^ 2))) ∧
        ∀ s ∈ Ico t (min (t + h) M.T),
          (∫⁻ ω, ENNReal.ofReal (Real.exp (C * (betaZ M W z t β s ω) ^ 2)) ∂P)
            ≤ ENNReal.ofReal (Real.sqrt 2 *
                Real.exp (ε * z ^ 2 + 3 * C * M.σ₀ ^ 4 * (M.ζ M.T ^ 2)⁻¹ * β ^ 2)) := by sorry

end SmoothAmbEq.Gaussian
