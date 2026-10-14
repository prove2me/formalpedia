-- Prove2me | Theorems.Thm_UnknownLoads_Refined_proposition_8
-- name    : UnknownLoads.Refined.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:05.499989+00:00
-- url     : https://prove2.me/theorems/5c7d78ee-a11d-4a08-a887-3b61b2758bbf
-- title:
--   Proposition 8 — on Ω_T, uₙ → u uniformly on [0, T]
-- statement:
--   For each $\omega\in\Omega_T$, the total masses $u_n(\omega)=\sum_{i\ge1}q_n(\omega,i)$ converge uniformly over $[0,T]$ to the function $u:[0,T]\to[0,\infty)$ of (4),
--   $$
--   u(0)=\sum_{i=1}^\infty q(0,i),\qquad u(t)=u(0)e^{-\mu t}+\int_0^t\rho(s)\mu e^{-\mu(t-s)}ds .
--   $$
--
--   This is the almost-sure functional law of large numbers for the infinite-server system formed by all pools, under the coupled construction.
--
--   Throughout, "for each $\omega\in\Omega_T$" is rendered as: for every constant $B_T$ and every outcome $\omega$ satisfying the nice-path predicate $\mathrm{IsNicePath}(B_T,\omega)$ of Proposition 7 (the standing initial conditions, the equations (9a)–(9b) with simple events for every $n\ge1$, the relative-compactness property of Proposition 4, (11) with some $n_T(\omega)$, and (12a)–(12c) for every $\gamma\in[0,1/2)$). Proposition 7 states that this predicate holds almost surely for some $B_T>0$.
--
--   **Formalization Note** $u_n$ is a real series; on nice outcomes it is a finite sum for $n\ge n_T(\omega)$, so the uniform limit is unaffected.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 28, Proposition 8 (proof in App. B, pp. 49–50)

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
import Definitions.Def_UnknownLoads_Refined_Load
import Definitions.Def_UnknownLoads_Refined_Construction
import Definitions.Def_UnknownLoads_Refined_System

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UnknownLoads.Refined

theorem proposition_8 (D : LoadData) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α : ℕ → ℝ}
    (sys : System D Ω P α)
    (BT : ℕ) (ω : Ω) (hω : sys.IsNicePath BT ω) :
    TendstoUniformlyOn (fun n t => sys.totalMass n ω t) (D.fluidU sys.q0) atTop
      (Icc 0 D.T) := by sorry

end UnknownLoads.Refined
