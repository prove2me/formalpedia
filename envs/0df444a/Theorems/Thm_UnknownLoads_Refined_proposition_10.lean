-- Prove2me | Theorems.Thm_UnknownLoads_Refined_proposition_10
-- name    : UnknownLoads.Refined.proposition_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:10.913327+00:00
-- url     : https://prove2.me/theorems/24cd4f72-f933-4738-912f-7d497296baa9
-- title:
--   Proposition 10 — on Ω_T, ℓₙ ≤ mΔ on [a + σ, b] for all large n, for every σ > σ_bd
-- statement:
--   Assume (5): $\lim_n\alpha_n=1$ and $\liminf_n n^{\gamma_0}(1-\alpha_n)>0$ for some $\gamma_0\in(0,1/2)$, and that the offered load is $(m,\Delta)$-bounded on $[a,b]$. Fix
--   $$
--   \sigma>\sigma_{\mathrm{bd}}(a,b,m,\Delta):=\begin{cases}\frac1\mu\Big[\log\Big(\frac{u(a)-\rho_{\max}}{(m+1)\Delta-\rho_{\max}}\Big)\Big]^+&\text{if }u(a)>\rho_{\max},\\0&\text{if }u(a)\le\rho_{\max}.\end{cases}
--   $$
--   Then for each $\omega\in\Omega_T$ there is $n_{\mathrm{bd}}(\omega)$ with
--   $$
--   \ell_n(\omega,t)\le m\Delta\qquad\text{for all }t\in[a+\sigma,b],\ n\ge n_{\mathrm{bd}}(\omega).
--   $$
--
--   This is the first half of the threshold's convergence: it cannot stay above $m\Delta$.
--
--   Throughout, "for each $\omega\in\Omega_T$" is rendered as: for every constant $B_T$ and every outcome $\omega$ satisfying the nice-path predicate $\mathrm{IsNicePath}(B_T,\omega)$ of Proposition 7 (the standing initial conditions, the equations (9a)–(9b) with simple events for every $n\ge1$, the relative-compactness property of Proposition 4, (11) with some $n_T(\omega)$, and (12a)–(12c) for every $\gamma\in[0,1/2)$). Proposition 7 states that this predicate holds almost surely for some $B_T>0$.
--
--   **Formalization Note** $\liminf_n n^{\gamma_0}(1-\alpha_n)>0$ is written as: there is $\kappa>0$ with $\kappa\le n^{\gamma_0}(1-\alpha_n)$ for all large $n$ (equivalent, and avoids a real `liminf` of a possibly unbounded sequence).
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 30, Proposition 10 (σ_bd as defined there)

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
import Definitions.Def_UnknownLoads_Refined_Load
import Definitions.Def_UnknownLoads_Refined_Construction
import Definitions.Def_UnknownLoads_Refined_System

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UnknownLoads.Refined

theorem proposition_10 (D : LoadData) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α : ℕ → ℝ}
    (sys : System D Ω P α)
    (γ₀ : ℝ) (hγ₀ : γ₀ ∈ Ioo (0 : ℝ) (1 / 2))
    (hα_lim : Tendsto α atTop (𝓝 1))
    (hα_rate : ∃ κ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, κ ≤ (n : ℝ) ^ γ₀ * (1 - α n))
    (m : ℕ) (a b : ℝ) (hbd : D.IsBounded sys.q0 m a b)
    (σ : ℝ) (hσ : D.sigmaBd sys.q0 a b m < σ)
    (BT : ℕ) (ω : Ω) (hω : sys.IsNicePath BT ω) :
    ∃ nbd : ℕ, ∀ n ≥ nbd, ∀ t ∈ Icc (a + σ) b, sys.ℓ n ω t ≤ m * D.Δ := by sorry

end UnknownLoads.Refined
