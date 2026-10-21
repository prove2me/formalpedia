-- Prove2me | Theorems.Thm_SGHMCOpt_Euler_eq_A21_second_term
-- name    : SGHMCOpt.Euler.eq_A21_second_term
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:15.99099+00:00
-- url     : https://prove2.me/theorems/3f548448-130c-4191-a4f7-15f52e3d23d6
-- title:
--   Proof of Corollary 4, p. 42 — second term of (A.21): E F(X̂*) − E F_Z(X̂*) ≤ 𝒥₃(n)
-- statement:
--   Assume parts (i)–(iii) of Assumption 1, a probability law $D$ on $\mathcal Z$, $n\ge1$, $\beta>0$ and a lower bound $\lambda_0>0$ of the uniform spectral gap (3.8). Let $Z\sim D^n$ and let $\hat X^*$ have conditional law $\pi_Z$ given $Z$ (its $x$-component). Then
--   $$\mathbb EF(\hat X^*)-\mathbb EF_Z(\hat X^*)\le\frac{4\beta c_{LS}}n\Big(\frac{M^2}m\Big(b+\frac d\beta\Big)+B^2\Big)=\mathcal J_3(n),$$
--   where $\mathbb EF(\hat X^*)=\int D^n(dz)\int F(x)\pi_z(dx,dv)$ and $\mathbb EF_Z(\hat X^*)=\int D^n(dz)\int F_z(x)\pi_z(dx,dv)$, and $c_{LS}$ is as in Lemma 27.
--
--   This is the generalisation error of the Gibbs algorithm, the second term of the decomposition (A.21) of the population risk; the paper obtains it from Lemma 27.
--
--   **Formalization Note** $c_{LS}$ is evaluated at $\lambda_0$, as in Lemma 27. Integrability of the two dataset-dependent expectations under $D^n$ is part of the conclusion.
-- source:
--   arXiv:1809.04618v4, proof of Corollary 4, (A.21) and the display on p. 42; (3.7), p. 12

import Mathlib
import Definitions.Def_SGHMCOpt_Euler_Constants
import Definitions.Def_SGHMCOpt_Euler_Model

open MeasureTheory

namespace SGHMCOpt.Euler

/-- Proof of Corollary 4, p. 42, the bound on the second term of (A.21):
`E F(X̂*) − E F_Z(X̂*) ≤ (4βc_LS/n)((M²/m)(b + d/β) + B²) = 𝒥₃(n)`, where `Z ∼ Dⁿ` and
`X̂* | Z = z` has the `x`-marginal of `π_z`. -/
theorem eq_A21_second_term {d n : ℕ} {𝒵 : Type*} [MeasurableSpace 𝒵] (f : E d → 𝒵 → ℝ)
    (D : Measure 𝒵) [IsProbabilityMeasure D] (p : Params) (lam0 : ℝ) (hn : 0 < n)
    (hloss : LossAssumption f p) (hβ : 0 < p.β) (hlam0 : 0 < lam0)
    (hP : HasPoincare n f p lam0) :
    Integrable (fun z : Fin n → 𝒵 => ∫ q, F f D q.1 ∂(gibbs p f z))
        (Measure.pi fun _ : Fin n => D) ∧
      Integrable (fun z : Fin n → 𝒵 => ∫ q, Fz f z q.1 ∂(gibbs p f z))
        (Measure.pi fun _ : Fin n => D) ∧
      ∫ z, ∫ q, F f D q.1 ∂(gibbs p f z) ∂(Measure.pi fun _ : Fin n => D) -
          ∫ z, ∫ q, Fz f z q.1 ∂(gibbs p f z) ∂(Measure.pi fun _ : Fin n => D) ≤
        J3 p d lam0 n := by sorry

end SGHMCOpt.Euler
