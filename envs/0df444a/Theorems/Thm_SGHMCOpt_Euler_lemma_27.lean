-- Prove2me | Theorems.Thm_SGHMCOpt_Euler_lemma_27
-- name    : SGHMCOpt.Euler.lemma_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:21.219392+00:00
-- url     : https://prove2.me/theorems/0587fec2-d059-4175-92af-c3d0a35785d8
-- title:
--   Lemma 27, p. 70 — uniform stability of π_z: sup_ζ |∫f(x,ζ)dπ_z − ∫f(x,ζ)dπ_z̄| ≤ (4βc_LS/n)((M²/m)(b + d/β) + B²)
-- statement:
--   Assume parts (i)–(iii) of Assumption 1, $n\ge1$, $\beta>0$, and let $\lambda_0>0$ be a lower bound of the uniform spectral gap $\lambda_*$ of (3.8). For any two datasets $z,\bar z\in\mathcal Z^n$ that differ in exactly one coordinate, $|\{i:z_i\ne\bar z_i\}|=1$, and every data point $\zeta\in\mathcal Z$,
--   $$\Big|\int f(x,\zeta)\,\pi_z(dx,dv)-\int f(x,\zeta)\,\pi_{\bar z}(dx,dv)\Big|\le\frac{4\beta c_{LS}}n\Big(\frac{M^2}m\Big(b+\frac d\beta\Big)+B^2\Big),$$
--   with
--   $$c_{LS}=\frac{2m^2+8M^2}{m^2M\beta}+\frac1{\lambda_0}\Big(\frac{6M(d+\beta)}m+2\Big).$$
--
--   The Gibbs algorithm is therefore uniformly stable, which bounds its generalisation error (Raginsky–Rakhlin–Telgarsky 2017, Proposition 12).
--
--   **Formalization Note** The paper takes $c_{LS}$ to be any constant below the displayed bound with $\lambda_*$; since the right side increases in $c_{LS}$, the statement uses the bound itself, with $\lambda_*$ replaced by a positive lower bound $\lambda_0$, encoded by `HasPoincare`. This avoids $1/\lambda_*$ when $\lambda_*$ is an infimum that could be $0$. The supremum over $\zeta$ is the bound for every $\zeta$. Integrability is part of the conclusion.
-- source:
--   arXiv:1809.04618v4, Lemma 27, p. 70 (citing Raginsky, Rakhlin, Telgarsky 2017, Proposition 12); (3.8), p. 12

import Mathlib
import Definitions.Def_SGHMCOpt_Euler_Constants
import Definitions.Def_SGHMCOpt_Euler_Model

open MeasureTheory

namespace SGHMCOpt.Euler

/-- Lemma 27, p. 70 (RRT17, Proposition 12): for two datasets `z, z̄ ∈ 𝒵ⁿ` that differ in exactly
one coordinate and every data point `ζ`,
`|∫ f(x, ζ) π_z(dx, dv) − ∫ f(x, ζ) π_z̄(dx, dv)| ≤ (4βc_LS/n)((M²/m)(b + d/β) + B²)`, with `c_LS` the
printed bound evaluated at a lower bound `λ₀ > 0` of the uniform spectral gap `λ_*`. -/
theorem lemma_27 {d n : ℕ} {𝒵 : Type*} [MeasurableSpace 𝒵] (f : E d → 𝒵 → ℝ) (p : Params)
    (lam0 : ℝ) (hn : 0 < n) (hloss : LossAssumption f p) (hβ : 0 < p.β) (hlam0 : 0 < lam0)
    (hP : HasPoincare n f p lam0) (z zbar : Fin n → 𝒵) (hz : {i : Fin n | z i ≠ zbar i}.ncard = 1)
    (ζ : 𝒵) :
    Integrable (fun q : E d × E d => f q.1 ζ) (gibbs p f z) ∧
      Integrable (fun q : E d × E d => f q.1 ζ) (gibbs p f zbar) ∧
      |∫ q, f q.1 ζ ∂(gibbs p f z) - ∫ q, f q.1 ζ ∂(gibbs p f zbar)| ≤
        4 * p.β * cLS p d lam0 / (n : ℝ) * (p.M ^ 2 / p.m * (p.b + (d : ℝ) / p.β) + p.B ^ 2) := by sorry

end SGHMCOpt.Euler
