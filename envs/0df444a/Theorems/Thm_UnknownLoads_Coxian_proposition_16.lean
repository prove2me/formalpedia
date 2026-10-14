-- Prove2me | Theorems.Thm_UnknownLoads_Coxian_proposition_16
-- name    : UnknownLoads.Coxian.proposition_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:58.53978+00:00
-- url     : https://prove2.me/theorems/1c1823a0-1a59-497c-91f5-717d7041bbd9
-- title:
--   Proposition 16 — there are B_T and a set Ω_T of probability one of nice sample paths satisfying (23) and (24a)–(24c)
-- statement:
--   Consider a system of the coupled construction of Section 6.1.1 and a horizon $T > 0$. There exist a positive integer $B_T$ and a set $\Omega_T \subset \Gamma_T$ of probability one such that:
--
--   1. for each $\omega \in \Omega_T$ there is $n_T(\omega)$ with
--   $$q_n(\omega, t, B_T+1) = 0 \quad\text{and}\quad \ell_n(\omega,t) \le B_T \qquad \text{for all } t\in[0,T] \text{ and all } n \ge n_T(\omega); \tag{23}$$
--   2. on $\Omega_T$,
--   $$\lim_{n\to\infty} s_n(0) = s(0), \tag{24a}$$
--   $$\lim_{n\to\infty}\sup_{t\in[0,T]}\Big|\frac1n\mathcal N^\lambda_n(t) - \lambda t\Big| = 0, \tag{24b}$$
--   $$\lim_{n\to\infty}\sup_{t\in[0,\mu_i\nu(i)T]}\Big|\frac1n\mathcal N_{(\nu,i,j)}(nt) - t\Big| = 0 \quad \text{for all } (\nu,i,j)\in\mathbb N^r\times\{1,\dots,r\}\times\{0,1\}. \tag{24c}$$
--
--   The set $\Omega_T$ is the set of well-behaved sample paths on which Propositions 17 and 18 and the proof of Theorem 3 operate.
--
--   **Formalization Note** Stated as $\exists B_T > 0$ such that almost every $\omega$ satisfies `IsNicePath sys T B_T ω`, the conjunction of membership in $\Gamma_0$ (the equations hold), Proposition 14's property ($\Gamma_T$), (23) and (24a)–(24c). In (24c) the interval is $[0, \mu_i\,\nu(i)\,T]$, the phase-$i$ rate times $\nu(i)$ times $T$.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 41, Proposition 16

import Mathlib
import Definitions.Def_UnknownLoads_Coxian_NicePaths
open MeasureTheory Filter Topology

namespace UnknownLoads.Coxian

/-- Proposition 16 (p. 41). For every horizon `T > 0` there is a positive `B_T ∈ ℕ` such that
almost every `ω` lies in `Ω_T`: the equations hold, Proposition 14's property holds, (23) holds
from some `n_T(ω)` on, and the limits (24a)–(24c) hold. -/
theorem proposition_16 {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μP : Measure Ω}
    (sys : System P Ω μP) (T : ℝ) (hT : 0 < T) :
    ∃ BT : ℕ, 0 < BT ∧ ∀ᵐ ω ∂μP, IsNicePath sys T BT ω := by sorry

end UnknownLoads.Coxian
