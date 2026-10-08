-- Prove2me | Theorems.Thm_PoissonDirichlet_Moments_eq_36
-- name    : PoissonDirichlet.Moments.eq_36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:47.04599+00:00
-- url     : https://prove2.me/theorems/b5d3af23-5130-4d91-9d3c-9fd055a6d9b9
-- title:
--   Proposition 11 (i), (36), p. 864 — E[exp(−λA_{n−1})] = φ_α(λ)^{n−1} under PD(α, 0)
-- statement:
--   Let $0<\alpha<1$ and let $(V_n)$ have the $\mathrm{PD}(\alpha,0)$ law, with $A_0=0$ and $A_n=(V_1+\dots+V_n)/V_{n+1}$ (31). For $n\ge1$ and $\lambda\ge0$,
--
--   $$E\big[\exp(-\lambda A_{n-1})\big]=\phi_\alpha(\lambda)^{n-1},$$
--
--   where $\phi_\alpha(\lambda)=\alpha\int_1^\infty e^{-\lambda x}x^{-\alpha-1}\,dx$ is (33).
--
--   This is the Laplace-transform part of Proposition 11 (i): $A_{n-1}$ is distributed as a sum of $n-1$ independent copies of $A_1$. It is the last ingredient of the proof of Lemma 27.
--
--   **Formalization Note** Indexing is from $0$: the Lean index $k$ is $n-1$. The integrand is bounded by $1$ because $A_{n-1}\ge0$ almost surely.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 864, Proposition 11 (i), (36)

import Mathlib
import Definitions.Def_PoissonDirichlet_Moments_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Moments

/-- Proposition 11 (i), (36), p. 864, 0-based (`k = n - 1`): under `PD(α, 0)`,
`E[exp(-λ A_{n-1})] = φ_α(λ)^{n-1}` for `λ ≥ 0`. -/
theorem eq_36 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α 0 P V)
    (l : ℝ) (hl : 0 ≤ l) (k : ℕ) :
    ∫ ω, Real.exp (-l * PoissonDirichlet.Wendel.Aseq (V ω) k) ∂P = PoissonDirichlet.Wendel.phi α l ^ k := by sorry

end PoissonDirichlet.Moments
