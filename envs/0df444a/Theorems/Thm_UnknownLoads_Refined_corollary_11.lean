-- Prove2me | Theorems.Thm_UnknownLoads_Refined_corollary_11
-- name    : UnknownLoads.Refined.corollary_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:12.009517+00:00
-- url     : https://prove2.me/theorems/13edd22d-572e-4820-be2e-6f328f1720ec
-- title:
--   Corollary 11 — on Ω_T, limsup sup_{[a+σ,b]} vₙ(t,(m+1)Δ+1) e^{µ[t−(a+σ)]} ≤ u(a+σ)
-- statement:
--   Under the assumptions of Theorem 2 (condition (5) and $(m,\Delta)$-boundedness on $[a,b]$), fix $\sigma>\sigma_{\mathrm{bd}}(a,b,m,\Delta)$. Then for all $\omega\in\Omega_T$,
--   $$
--   \limsup_{n\to\infty}\ \sup_{t\in[a+\sigma,b]}\ v_n(\omega,t,(m+1)\Delta+1)\,e^{\mu[t-(a+\sigma)]}\le u(a+\sigma),
--   $$
--   where $v_n(t,j)=\sum_{i\ge j}q_n(t,i)$.
--
--   This gives (6c) of Theorem 2 with the constant $c=u(a+\sigma)$.
--
--   Throughout, "for each $\omega\in\Omega_T$" is rendered as: for every constant $B_T$ and every outcome $\omega$ satisfying the nice-path predicate $\mathrm{IsNicePath}(B_T,\omega)$ of Proposition 7 (the standing initial conditions, the equations (9a)–(9b) with simple events for every $n\ge1$, the relative-compactness property of Proposition 4, (11) with some $n_T(\omega)$, and (12a)–(12c) for every $\gamma\in[0,1/2)$). Proposition 7 states that this predicate holds almost surely for some $B_T>0$.
--
--   **Formalization Note** The tail mass, the supremum and the limit superior are taken in $[0,\infty]$ (no summability or boundedness caveats); the right side is $u(a+\sigma)\ge0$ embedded in $[0,\infty]$. Condition (5) is rendered as in Proposition 10.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 32, Corollary 11

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
import Definitions.Def_UnknownLoads_Refined_Load
import Definitions.Def_UnknownLoads_Refined_Construction
import Definitions.Def_UnknownLoads_Refined_System

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UnknownLoads.Refined

theorem corollary_11 (D : LoadData) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α : ℕ → ℝ}
    (sys : System D Ω P α)
    (γ₀ : ℝ) (hγ₀ : γ₀ ∈ Ioo (0 : ℝ) (1 / 2))
    (hα_lim : Tendsto α atTop (𝓝 1))
    (hα_rate : ∃ κ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, κ ≤ (n : ℝ) ^ γ₀ * (1 - α n))
    (m : ℕ) (a b : ℝ) (hbd : D.IsBounded sys.q0 m a b)
    (σ : ℝ) (hσ : D.sigmaBd sys.q0 a b m < σ)
    (BT : ℕ) (ω : Ω) (hω : sys.IsNicePath BT ω) :
    Filter.limsup (fun n : ℕ => ⨆ t ∈ Icc (a + σ) b,
        sys.tailMassE n ω t ((m + 1) * D.Δ + 1) *
          ENNReal.ofReal (Real.exp (D.mu * (t - (a + σ))))) atTop ≤
      ENNReal.ofReal (D.fluidU sys.q0 (a + σ)) := by sorry

end UnknownLoads.Refined
