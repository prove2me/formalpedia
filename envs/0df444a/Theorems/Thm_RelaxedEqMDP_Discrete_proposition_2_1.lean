-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_proposition_2_1
-- name    : RelaxedEqMDP.Discrete.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:46.315184+00:00
-- url     : https://prove2.me/theorems/d3e591a5-12a9-4ff9-88b5-b18897ae3985
-- title:
--   Proposition 2.1, p. 7 — $\pi\in\Pi_r$ is a regular relaxed equilibrium iff $\Phi_\lambda(\pi)=\pi$
-- statement:
--   Throughout, $U\subset\mathbb R^\ell$ ($\ell\ge1$) is a compact action space with $\mathrm{Leb}(U)>0$, the state space is $\mathcal S=\{1,\dots,d\}$, $p^u=(p^u_{ij})$ is the transition matrix of the chain under action $u\in U$ with $i$-th row $p^u_i$, and $f(t,i,u)$ is the reward.
--
--   Let Assumption 2.1 hold and $\lambda>0$. For every regular relaxed control $\pi\in\Pi_r$,
--   $$\pi\ \text{is a regular relaxed equilibrium for (2.4)}\iff\Phi_\lambda(\pi)=\pi,$$
--   where $\Phi_\lambda(\pi)=\Gamma_\lambda(V^\pi_\lambda,\cdot)$ is the Gibbs best response to $\pi$.
--
--   The proposition turns the equilibrium condition (2.7), which quantifies over all deviations, into a single-valued fixed-point equation.
--
--   **Formalization Note** Equality $\Phi_\lambda(\pi)=\pi$ is equality of the measures $\pi(i)$ for every $i$ (densities equal almost everywhere on $U$). Measurability of $u\mapsto f(t,i,u)$ and $u\mapsto p^u_{ij}$ is assumed.
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 7, Proposition 2.1

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete

/-- Proposition 2.1, p. 7: under Assumption 2.1, for any `λ > 0`, a regular control `π` is a
regular relaxed equilibrium if and only if `Φ_λ(π) = π`. -/
theorem proposition_2_1 {d ℓ : ℕ} (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ)
    (hS : Standing U p) (hM : MeasMaps f p) (h21 : Assumption21 U f δ) (lam : ℝ) (hlam : 0 < lam)
    (pol : Control d ℓ) (hpol : IsRegular U pol) :
    IsRegularRelaxedEq U p f δ lam pol ↔ PhiLam U p f δ lam pol = pol := by sorry
end RelaxedEqMDP.Discrete
