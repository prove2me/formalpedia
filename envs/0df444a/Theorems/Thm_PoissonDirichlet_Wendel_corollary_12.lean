-- Prove2me | Theorems.Thm_PoissonDirichlet_Wendel_corollary_12
-- name    : PoissonDirichlet.Wendel.corollary_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:45.156074+00:00
-- url     : https://prove2.me/theorems/ffe1fc0c-1055-4d45-a6b0-78aafd2c75e4
-- title:
--   Corollary 12 (38), p. 864 — Wendel's formula E[exp(−λ/V_n)] = e^{−λ} φ_α(λ)^{n−1} ψ_α(λ)^{−n}
-- statement:
--   Let $0<\alpha<1$ and let $(V_n)$ have the $\mathrm{PD}(\alpha,0)$ distribution, with $\phi_\alpha,\psi_\alpha$ as in (33)–(34). Then for every $n\ge1$ and $\lambda\ge0$,
--   $$E\left[\exp(-\lambda/V_n)\right]=\exp(-\lambda)\,\phi_\alpha(\lambda)^{n-1}\,\psi_\alpha(\lambda)^{-n}.$$
--
--   This is the Laplace transform of $1/V_n$ found by Darling and Lamperti ($n=1$) and Wendel ($n\ge2$); by uniqueness of Laplace transforms it determines the distribution of $V_n$.
--
--   **Formalization Note** Only the formula (38) is stated; the clause "the distribution of $V_n$ is determined by" it is uniqueness of the Laplace transform of the positive variable $1/V_n$, a general fact. 0-based: `V ω k` is $V_{k+1}$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 864, Corollary 12, (38)

import Mathlib
import Definitions.Def_PoissonDirichlet_Wendel_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Wendel

/-- Corollary 12, (38), p. 864: for `V` with law PD(α, 0), 0 < α < 1, n = k + 1 and λ ≥ 0,
`E[exp(-λ / V_n)] = exp(-λ) φ_α(λ)^{n-1} ψ_α(λ)^{-n}`. Only the formula is stated; that it
determines the law of `V_n` is uniqueness of Laplace transforms. 0-based: `V ω k` is `V_n`. -/
theorem corollary_12 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α 0 P V) (k : ℕ)
    (l : ℝ) (hl : 0 ≤ l) :
    ∫ ω, Real.exp (-l / V ω k) ∂P = Real.exp (-l) * phi α l ^ k * (psi α l ^ (k + 1))⁻¹ := by sorry

end PoissonDirichlet.Wendel
