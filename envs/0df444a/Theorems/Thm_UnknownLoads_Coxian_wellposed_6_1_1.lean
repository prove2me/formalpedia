-- Prove2me | Theorems.Thm_UnknownLoads_Coxian_wellposed_6_1_1
-- name    : UnknownLoads.Coxian.wellposed_6_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:56.828203+00:00
-- url     : https://prove2.me/theorems/023848c5-c416-4870-8e8f-d5d6eb2a045a
-- title:
--   §6.1.1, pp. 39–40 — the coupled construction is well posed: almost surely (21a)–(21b) have a unique càdlàg solution for every n
-- statement:
--   Fix stochastic primitives as in Section 6.1.1: independent unit-rate Poisson processes $\mathcal N_{(\nu,i,j)}$, i.i.d. uniform selection variables $U_j$ on $[0,1)$, and random initial occupancy states $s_n(0)$ satisfying the assumptions of Section 3, the three families being independent.
--
--   Then, with probability one, for every $n \ge 1$:
--
--   1. there exist a càdlàg occupancy path $s : [0,\infty) \to S$ with finitely many tasks at every time and a threshold path $\ell : [0,\infty) \to \mathbb N$ such that
--   $$s(t) = s_n(0) + \bar{\mathcal A}_n(t) + \bar{\mathcal P}_n(t) + \bar{\mathcal D}_n(t), \qquad \ell(t) = \lfloor u(t) \rfloor_\Delta \qquad \text{for all } t \ge 0;$$
--   2. any two such solutions coincide at every time $t \ge 0$.
--
--   This is the statement that the coupled construction defines the occupancy and threshold processes; it guarantees that the notion of a system used by all other results of the mission is not vacuous and that it describes the paper's processes.
--
--   **Formalization Note** The paper states this in prose ("As in Section 5.1.1, it is possible to construct càdlàg processes $s_n$ and $\ell_n$ such that the following equations hold on a set of probability one $\Gamma_0$ …", referring to the existence and uniqueness claim of Section 5.1.1). Existence and uniqueness are both posed, on $t \ge 0$; values at negative times are irrelevant.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, pp. 39–40, Section 6.1.1 (unnumbered; with the uniqueness claim of Section 5.1.1, p. 24)

import Mathlib
import Definitions.Def_UnknownLoads_Coxian_Construction
open MeasureTheory Filter Topology

namespace UnknownLoads.Coxian

/-- Well-posedness of the coupled construction (§6.1.1, pp. 39–40): almost surely, for every
`n ≥ 1`, the equations (21a)–(21b) have a solution `(s, ℓ)` (càdlàg, `S`-valued, finitely many
tasks), and any two solutions agree at every time `t ≥ 0`. -/
theorem wellposed_6_1_1 {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μP : Measure Ω}
    (prim : Primitives P Ω μP) :
    ∀ᵐ ω ∂μP, ∀ n : ℕ, 1 ≤ n →
      (∃ (s : ℝ → Profile P.r → ℝ) (ℓ : ℝ → ℕ), Solves prim n ω s ℓ) ∧
      ∀ (s s' : ℝ → Profile P.r → ℝ) (ℓ ℓ' : ℝ → ℕ),
        Solves prim n ω s ℓ → Solves prim n ω s' ℓ' → ∀ t : ℝ, 0 ≤ t → s t = s' t ∧ ℓ t = ℓ' t := by sorry

end UnknownLoads.Coxian
