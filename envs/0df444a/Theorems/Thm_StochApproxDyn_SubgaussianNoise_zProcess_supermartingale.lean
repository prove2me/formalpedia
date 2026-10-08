-- Prove2me | Theorems.Thm_StochApproxDyn_SubgaussianNoise_zProcess_supermartingale
-- name    : StochApproxDyn.SubgaussianNoise.zProcess_supermartingale
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:09:31.166981+00:00
-- url     : https://prove2.me/theorems/85ea3d85-449c-4b4f-afef-dcb382b5de96
-- title:
--   The exponential process $Z_n(\theta)$ is a supermartingale
-- statement:
--   Let $\{x_n\}$ given by $x_{n+1}-x_n=\gamma_{n+1}(F(x_n)+U_{n+1})$ be a Robbins–Monro algorithm on $(\Omega,\mathcal F,P)$ with filtration $\{\mathcal F_n\}$, and suppose the noise $\{U_n\}$ is subgaussian with constant $\Gamma>0$: $E(\exp\langle\theta,U_{n+1}\rangle\mid\mathcal F_n)\le\exp(\frac\Gamma2\|\theta\|^2)$ for all $n$ and $\theta\in\mathbb R^d$. For $\theta\in\mathbb R^d$ put
--   $$Z_n(\theta)=\exp\Big[\sum_{i=1}^n\langle\theta,\gamma_iU_i\rangle-\frac\Gamma2\sum_{i=1}^n\gamma_i^2\|\theta\|^2\Big],\qquad n\ge0,$$
--   with $Z_0(\theta)=1$. Then, for every $\theta\in\mathbb R^d$, $\{Z_n(\theta)\}_{n\ge0}$ is a supermartingale with respect to $\{\mathcal F_n\}$: each $Z_n(\theta)$ is $\mathcal F_n$-measurable and integrable, and $E(Z_{n+1}(\theta)\mid\mathcal F_n)\le Z_n(\theta)$ almost surely.
--
--   This exponential supermartingale is the starting point of the proof of Proposition 4.4: a maximal inequality applied to it gives Gaussian tail bounds for the weighted noise sums.
--
--   **Formalization Note** The paper defines $Z_n(\theta)$ for $n\ge1$; the statement also includes $n=0$ with empty sums. The supermartingale is Mathlib's `Supermartingale` for the filtration indexed by $\mathbb N$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 4.2, proof of Proposition 4.4, p. 17 (PDF p. 18), definition of Z_n(θ) and the sentence 'By the assumption on {U_n}, {Z_n(θ)} is a supermartingale'

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro
import Definitions.Def_StochApproxDyn_SubgaussianNoise_Subgaussian

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace StochApproxDyn.SubgaussianNoise

/-- Benaïm 1999, §4.2, proof of Proposition 4.4, p. 17: for a Robbins–Monro algorithm whose
noise is subgaussian with constant `Γ`, and every `θ ∈ ℝ^d`, the process
`Z_n(θ) = exp[∑_{i=1}^n ⟨θ, γ_i U_i⟩ − (Γ/2) ∑_{i=1}^n γ_i² ‖θ‖²]`
is a supermartingale with respect to `(ℱ_n)`. The paper defines `Z_n` for `n ≥ 1`; the index
`n = 0` (empty sums, `Z_0 = 1`) is included here. -/
theorem zProcess_supermartingale {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ)
    (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hRM : StochApproxDyn.MartingaleNoise.IsRobbinsMonro P ℱ F γ x U)
    (Γ : ℝ) (hΓ : 0 < Γ) (hsg : IsSubgaussianWith P ℱ U Γ)
    (θ : EuclideanSpace ℝ (Fin d)) :
    Supermartingale
      (fun (n : ℕ) (ω : Ω) =>
        Real.exp (∑ i ∈ Finset.range n, ⟪θ, γ (i + 1) • U (i + 1) ω⟫_ℝ
          - Γ / 2 * ∑ i ∈ Finset.range n, γ (i + 1) ^ 2 * ‖θ‖ ^ 2))
      ℱ P := by sorry

end StochApproxDyn.SubgaussianNoise
