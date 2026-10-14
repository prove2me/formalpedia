-- Prove2me | Theorems.Thm_UnknownLoads_Refined_theorem_2
-- name    : UnknownLoads.Refined.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:18.988151+00:00
-- url     : https://prove2.me/theorems/ea867c15-c0f6-453e-953f-0258cc74a97c
-- title:
--   Theorem 2 — under (5) and (m, Δ)-bounded load on [a, b], the threshold settles at mΔ and the load balances on [a + σ, b]
-- statement:
--   Consider the coupled sequence of systems with exponential service of rate $\mu$, arrival rate $n\lambda(t)$, the threshold dispatching rule with parameter $\Delta$, and the refined learning scheme with control parameters $\alpha_n\in(0,1)$. Suppose there is $\gamma_0\in(0,1/2)$ with
--   $$
--   \lim_{n\to\infty}\alpha_n=1\qquad\text{and}\qquad\liminf_{n\to\infty}n^{\gamma_0}(1-\alpha_n)>0. \tag{5}
--   $$
--   If the offered load is $(m,\Delta)$-bounded on $[a,b]$ and $\sigma(a,b,m,\Delta)<\sigma<b-a$, then with probability one
--   $$
--   \lim_{n\to\infty}\sup_{t\in[a+\sigma,b]}|\ell_n(t)-m\Delta|=0, \tag{6a}
--   $$
--   $$
--   \lim_{n\to\infty}\sup_{t\in[a+\sigma,b]}n^\gamma|1-q_n(t,i)|=0\qquad\text{for all }i\le m\Delta\text{ and all }\gamma\in[0,1/2), \tag{6b}
--   $$
--   $$
--   \limsup_{n\to\infty}\sup_{t\in[a+\sigma,b]}\sum_{i>(m+1)\Delta}q_n(t,i)\,e^{\mu[t-(a+\sigma)]}\le c, \tag{6c}
--   $$
--   with $c=u(a+\sigma)$, where $u$ is the fluid total mass (4).
--
--   Since the threshold is integer-valued, (6a) means that $\ell_n(t)=m\Delta$ on $[a+\sigma,b]$ for all large $n$: the learning scheme finds the threshold that balances the unknown load. By (6b) and (6c), the fraction of pools with fewer than $m\Delta$ tasks is $o(n^{-\gamma})$, and the mass beyond column $(m+1)\Delta$ decays exponentially.
--
--   **Formalization Note** The constant is fixed to the paper's $c=u(a+\sigma)$ (which is positive here), a stronger form than "there exists $c>0$". The set of probability one does not depend on $i$ or $\gamma$. (6a) and (6b) are in $\varepsilon$–$n$ form; in (6c) the series, the supremum and the limit superior are in $[0,\infty]$. $\liminf_n n^{\gamma_0}(1-\alpha_n)>0$ is written as $\exists\kappa>0$ with $\kappa\le n^{\gamma_0}(1-\alpha_n)$ eventually.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, pp. 15–16, Theorem 2 (with Definition 1, p. 15, and (4), p. 14)

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
import Definitions.Def_UnknownLoads_Refined_Load
import Definitions.Def_UnknownLoads_Refined_Construction
import Definitions.Def_UnknownLoads_Refined_System

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UnknownLoads.Refined

theorem theorem_2 (D : LoadData) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α : ℕ → ℝ}
    (sys : System D Ω P α)
    (γ₀ : ℝ) (hγ₀ : γ₀ ∈ Ioo (0 : ℝ) (1 / 2))
    (hα_lim : Tendsto α atTop (𝓝 1))
    (hα_rate : ∃ κ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, κ ≤ (n : ℝ) ^ γ₀ * (1 - α n))
    (m : ℕ) (a b : ℝ) (hbd : D.IsBounded sys.q0 m a b)
    (σ : ℝ) (hσ₁ : D.sigma sys.q0 a b m < σ) (hσ₂ : σ < b - a) :
    ∀ᵐ ω ∂P,
      (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc (a + σ) b,
          |(sys.ℓ n ω t : ℝ) - (m : ℝ) * D.Δ| ≤ ε) ∧
      (∀ i : ℕ, i ≤ m * D.Δ → ∀ γ ∈ Ico (0 : ℝ) (1 / 2), ∀ ε > (0 : ℝ),
          ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc (a + σ) b, (n : ℝ) ^ γ * |1 - sys.q n ω t i| ≤ ε) ∧
      Filter.limsup (fun n : ℕ => ⨆ t ∈ Icc (a + σ) b,
          (∑' i, ENNReal.ofReal (sys.q n ω t (i + ((m + 1) * D.Δ + 1)))) *
            ENNReal.ofReal (Real.exp (D.mu * (t - (a + σ))))) atTop ≤
        ENNReal.ofReal (D.fluidU sys.q0 (a + σ)) := by sorry

end UnknownLoads.Refined
