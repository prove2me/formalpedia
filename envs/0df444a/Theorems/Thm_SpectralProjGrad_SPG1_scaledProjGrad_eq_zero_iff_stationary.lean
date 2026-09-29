-- Prove2me | Theorems.Thm_SpectralProjGrad_SPG1_scaledProjGrad_eq_zero_iff_stationary
-- name    : SpectralProjGrad.SPG1.scaledProjGrad_eq_zero_iff_stationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:49:31.914301+00:00
-- url     : https://prove2.me/theorems/2c6dba6c-4b9d-4050-83a0-493760c5e377
-- title:
--   Lemma 2.1 (ii): $g_t(\bar x)=0$ iff $\bar x$ is constrained stationary
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ be closed and convex, let $f$ have continuous partial derivatives on an open set $U\supseteq\Omega$, with gradient $g=\nabla f$, and let $P$ be the orthogonal projection onto $\Omega$. Let $0<\alpha_{\min}<\alpha_{\max}$. For every $\bar x\in\Omega$ and every $t\in(0,\alpha_{\max}]$,
--
--   $$
--   g_t(\bar x)=P\bigl(\bar x-t\,g(\bar x)\bigr)-\bar x=0
--   \iff
--   \langle g(\bar x),x-\bar x\rangle\ge0\ \text{ for all } x\in\Omega .
--   $$
--
--   So the vanishing of the scaled projected gradient is exactly first-order stationarity; with $t=1$ it justifies the stopping test of Step 1 of SPG1.
--
--   **Formalization Note** The standing assumptions of the paper (closed convex $\Omega$, $f$ of class $C^1$ on an open $U\supseteq\Omega$) and the parameter constraint $0<\alpha_{\min}<\alpha_{\max}$ are carried as hypotheses exactly as on p. 3.
-- source:
--   Birgin, Martínez & Raydan, Nonmonotone Spectral Projected Gradient Methods on Convex Sets, authors' updated version (July 2004) of SIAM J. Optim. 10(4) (2000), https://www.ime.unicamp.br/~martinez/bmr.pdf, p. 5, Lemma 2.1 (ii)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_SpectralProjGrad_Shared_scaledProjGrad
import Definitions.Def_SpectralProjGrad_Shared_IsConstrainedStationary

namespace SpectralProjGrad.SPG1

/-- Lemma 2.1 (ii): for `x̄ ∈ Ω` and `t ∈ (0, α_max]`, the scaled projected gradient
`g_t(x̄) = P(x̄ - t ∇f(x̄)) - x̄` vanishes iff `x̄` is a constrained stationary point. -/
theorem scaledProjGrad_eq_zero_iff_stationary {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {αmin αmax : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hαmin : 0 < αmin) (hαmin_lt : αmin < αmax)
    (t : ℝ) (ht : t ∈ Set.Ioc 0 αmax)
    (xbar : EuclideanSpace ℝ (Fin n)) (hxbar : xbar ∈ Ω) :
    SpectralProjGrad.Shared.scaledProjGrad P f t xbar = 0 ↔ SpectralProjGrad.Shared.IsConstrainedStationary Ω f xbar := by sorry

end SpectralProjGrad.SPG1
