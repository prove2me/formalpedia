-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_eq_2_11_2_12
-- name    : RelaxedEqMDP.Discrete.eq_2_11_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:36.659017+00:00
-- url     : https://prove2.me/theorems/50546186-90b5-4610-aa6f-88367b2a4198
-- title:
--   (2.11)–(2.12), p. 6 — the Gibbs density $\Gamma_\lambda(y,i)$ is the unique maximizer of the one-step entropy-regularized objective
-- statement:
--   Throughout, $U\subset\mathbb R^\ell$ ($\ell\ge1$) is a compact action space with $\mathrm{Leb}(U)>0$, the state space is $\mathcal S=\{1,\dots,d\}$, $p^u=(p^u_{ij})$ is the transition matrix of the chain under action $u\in U$ with $i$-th row $p^u_i$, and $f(t,i,u)$ is the reward.
--
--   Let Assumption 2.1 hold, $\lambda>0$, $y\in\mathbb R^d$ and $i\in\mathcal S$. The Gibbs density
--   $$\Gamma_\lambda(y,i)(u)=\frac{e^{\frac1\lambda(f(0,i,u)+p^u_i\cdot y)}}{\int_U e^{\frac1\lambda(f(0,i,v)+p^v_i\cdot y)}\,dv},\qquad u\in U,$$
--   is a positive probability density on $U$ with finite entropy, and it is the unique maximizer of
--   $$\rho\;\longmapsto\;\int_U\big(f(0,i,u)-\lambda\ln(\rho(u))+p^u_i\cdot y\big)\rho(u)\,du$$
--   over densities $\rho$ on $U$ with $\int_U|\rho\ln\rho|\,du<\infty$: every such $\rho$ has objective value at most that of $\Gamma_\lambda(y,i)$, with equality only if $\rho=\Gamma_\lambda(y,i)$ almost everywhere on $U$.
--
--   With $y=V^\pi_\lambda$ this is the paper's statement that the maximizer set in (2.11) is the singleton $\{\rho^*_i\}$, which leads to the definition (2.12) of $\Gamma_\lambda$ and to the operator $\Phi_\lambda$.
--
--   **Formalization Note** The page states the claim for $y=V^\pi_\lambda$; it is posed for every $y\in\mathbb R^d$, the domain of (2.12). Densities are restricted to those with $\rho\ln\rho$ integrable on $U$ (finite entropy); for the others the objective is $-\infty$ or undefined. Lean's $\ln 0=0$ gives the convention $0\ln0=0$. Measurability of $u\mapsto f(0,i,u)$ and $u\mapsto p^u_{ij}$ is assumed.
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 6, (2.11)–(2.12) and the sentence between them

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete

/-- (2.11)–(2.12), p. 6: for `λ > 0` and `y ∈ ℝ^d`, `Γ_λ(y,i)` is a density on `U` with finite
entropy, and it is the unique maximizer, among densities `ρ` on `U` with `ρ ln ρ` integrable, of
`∫_U (f(0,i,u) − λ ln ρ(u) + p^u_i · y) ρ(u) du` (uniqueness up to Lebesgue-null sets). -/
theorem eq_2_11_2_12 {d ℓ : ℕ} (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ)
    (hS : Standing U p) (hM : MeasMaps f p) (h21 : Assumption21 U f δ) (lam : ℝ) (hlam : 0 < lam)
    (y : Fin d → ℝ) (i : Fin d) :
    ((∀ u ∈ U, 0 < gibbsDensity U f p lam y i u) ∧
      IntegrableOn (gibbsDensity U f p lam y i) U ∧
      ∫ u in U, gibbsDensity U f p lam y i u = 1 ∧
      IntegrableOn (fun u => gibbsDensity U f p lam y i u *
        Real.log (gibbsDensity U f p lam y i u)) U) ∧
    ∀ ρ : A ℓ → ℝ, (∀ u ∈ U, 0 ≤ ρ u) → IntegrableOn ρ U → ∫ u in U, ρ u = 1 →
      IntegrableOn (fun u => ρ u * Real.log (ρ u)) U →
        gibbsObjective U f p lam y i ρ ≤ gibbsObjective U f p lam y i (gibbsDensity U f p lam y i) ∧
        (gibbsObjective U f p lam y i ρ =
            gibbsObjective U f p lam y i (gibbsDensity U f p lam y i) →
          ρ =ᵐ[volume.restrict U] gibbsDensity U f p lam y i) := by sorry
end RelaxedEqMDP.Discrete
