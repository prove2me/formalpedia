-- Prove2me | Theorems.Thm_UnknownLoads_Refined_proposition_7
-- name    : UnknownLoads.Refined.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:03.135829+00:00
-- url     : https://prove2.me/theorems/d4d2e67b-3bf2-4cc9-b14e-39a4819a1418
-- title:
--   Proposition 7 — the set Ω_T of nice sample paths has probability one
-- statement:
--   For the coupled sequence of systems, there are a constant $B_T\in\mathbb N$, $B_T>0$, and a set $\Omega_T\subset\Gamma_T$ of probability one such that
--
--   (a) for each $\omega\in\Omega_T$ there is $n_T(\omega)$ with
--   $$
--   q_n(\omega,t,B_T+1)=0\quad\text{and}\quad \ell_n(\omega,t)\le B_T\quad\text{for all }t\in[0,T],\ n\ge n_T(\omega);
--   $$
--   (b) on $\Omega_T$, for all $\gamma\in[0,1/2)$,
--   $$
--   \lim_{n\to\infty}q_n(0)=q(0),\qquad \lim_{n\to\infty}\sup_{t\in[0,T]}n^\gamma\Big|\frac1n\mathcal N^\lambda_n(t)-\int_0^t\lambda(s)ds\Big|=0,\qquad \lim_{n\to\infty}\sup_{t\in[0,\mu iT]}n^\gamma\Big|\frac1n\mathcal N_i(nt)-t\Big|=0\ \ (i\ge1).
--   $$
--
--   Every pathwise result of §5 is proved for the outcomes of $\Omega_T$.
--
--   **Formalization Note** The conclusion is that, for some $B_T>0$, almost every outcome satisfies the nice-path predicate, which also records $\omega\in\Gamma_T$ (Proposition 4's property), the equations (9a)–(9b) and simple events for every $n$, and the initial-condition assumptions at $\omega$ — all probability-one properties.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, pp. 27–28, Proposition 7

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
import Definitions.Def_UnknownLoads_Refined_Load
import Definitions.Def_UnknownLoads_Refined_Construction
import Definitions.Def_UnknownLoads_Refined_System

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UnknownLoads.Refined

theorem proposition_7 (D : LoadData) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α : ℕ → ℝ}
    (sys : System D Ω P α) :
    ∃ BT : ℕ, 0 < BT ∧ ∀ᵐ ω ∂P, sys.IsNicePath BT ω := by sorry

end UnknownLoads.Refined
