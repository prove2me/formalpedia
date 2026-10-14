-- Prove2me | Theorems.Thm_UnknownLoads_Refined_lemma_22
-- name    : UnknownLoads.Refined.lemma_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:07.205431+00:00
-- url     : https://prove2.me/theorems/e8f48f14-7c32-4fa6-9750-4fa957ebee0b
-- title:
--   Lemma 22 — 𝒜ₙ(i) and 𝒟ₙ(i) lie in L^{ε_{i,n}}_{M_i} with ε_{i,n} → 0
-- statement:
--   Fix an outcome $\omega$ of the coupled construction at which the initial-condition assumptions hold, $(q_n(\omega),\ell_n(\omega))$ solves (9a)–(9b) for every $n\ge1$, and
--   $$
--   \lim_{n\to\infty}q_n(0)=q(0),\qquad \lim_{n\to\infty}\sup_{t\in[0,T]}\Big|\frac1n\mathcal N^\lambda_n(t)-\int_0^t\lambda(s)ds\Big|=0,\qquad \lim_{n\to\infty}\sup_{t\in[0,\mu iT]}\Big|\frac1n\mathcal N_i(nt)-t\Big|=0\ \ (i\ge1)
--   $$
--   ((30a)–(30c), i.e. $\omega\in\Gamma_T$ of Proposition 19). Then for every $i\ge0$ there are $M_i>0$ and a sequence $\varepsilon_{i,n}>0$ with $\varepsilon_{i,n}\to0$ such that, for all $n\ge1$,
--   $$
--   \mathcal A_n(i)\in L^{\varepsilon_{i,n}}_{M_i}\qquad\text{and}\qquad \mathcal D_n(i)\in L^{\varepsilon_{i,n}}_{M_i}.
--   $$
--
--   Together with Lemma 21 this yields the relative compactness of Proposition 4.
--
--   **Formalization Note** The functions are evaluated at the fixed $\omega$; $L^\varepsilon_M$ is the set of càdlàg functions on $[0,T]$ vanishing at $0$ with $|x(t)-x(s)|\le M|t-s|+\varepsilon$.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 47, Lemma 22 (with Proposition 19, (30a)–(30c), p. 46)

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
import Definitions.Def_UnknownLoads_Refined_Load
import Definitions.Def_UnknownLoads_Refined_Construction
import Definitions.Def_UnknownLoads_Refined_System

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UnknownLoads.Refined

theorem lemma_22 (D : LoadData) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α : ℕ → ℝ}
    (sys : System D Ω P α)
    (ω : Ω) (hinit : sys.InitAt ω)
    (hsol : ∀ n : ℕ, 1 ≤ n → sys.Solves (α n) n ω (sys.q n ω) (sys.ℓ n ω))
    (h30a : ∀ i, Tendsto (fun n => sys.q n ω 0 i) atTop (𝓝 (sys.q0 i)))
    (h30b : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc 0 D.T,
      |(1 / (n : ℝ)) * (sys.arrivals n ω t : ℝ) - D.cumRate t| ≤ ε)
    (h30c : ∀ i : ℕ, 1 ≤ i → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ Icc 0 (D.mu * i * D.T), |(1 / (n : ℝ)) * ((sys.N i).count ((n : ℝ) * t) ω : ℝ) - t| ≤ ε) :
    ∀ i : ℕ, ∃ M > (0 : ℝ), ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n →
        LipSet D.T M (ε n) (fun t => sys.arr n ω t i) ∧
        LipSet D.T M (ε n) (fun t => sys.dep n ω t i) := by sorry

end UnknownLoads.Refined
