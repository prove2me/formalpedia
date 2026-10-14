-- Prove2me | Theorems.Thm_UnknownLoads_Coxian_proposition_14
-- name    : UnknownLoads.Coxian.proposition_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:49.606288+00:00
-- url     : https://prove2.me/theorems/d59b6bd6-43cc-4ce2-9844-64167124a722
-- title:
--   Proposition 14 — almost surely the arrival, transition, departure and occupancy processes are relatively compact with Lipschitz limits
-- statement:
--   Consider a system of the coupled construction of Section 6.1.1 and a horizon $T > 0$. There is a set $\Gamma_T$ of probability one such that, for each $\omega \in \Gamma_T$ and each phase $m$, the sequences
--   $$\{\mathcal A_n(\omega) : n\ge1\},\quad \{\mathcal P_n(\omega,m) : n \ge 1\},\quad \{\mathcal D_n(\omega,m) : n\ge 1\},\quad \{s_n(\omega) : n\ge1\}$$
--   are relatively compact with respect to $\varrho$ (coordinatewise uniform convergence on $[0,T]$), and the limit of every convergent subsequence has Lipschitz coordinates.
--
--   This is the compactness step of the fluid-limit argument: Proposition 18 and the proof of Theorem 3 extract convergent subsequences of the occupancy processes and use that their limits are Lipschitz, hence absolutely continuous.
--
--   **Formalization Note** Stated as: for every $T > 0$, almost surely `Prop14Property sys T ω`; relative compactness is rendered sequentially (see the `NicePaths` definition). The paper omits the proof ("analogous to that of Proposition 4").
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 40, Proposition 14

import Mathlib
import Definitions.Def_UnknownLoads_Coxian_NicePaths
open MeasureTheory Filter Topology

namespace UnknownLoads.Coxian

/-- Proposition 14 (p. 40). For every horizon `T > 0`, almost surely the sequences `{𝒜_n(ω)}`,
`{𝒫_n(ω, m)}`, `{𝒟_n(ω, m)}` and `{s_n(ω)}` are relatively compact with respect to `ϱ` on
`[0, T]` and every subsequential limit has Lipschitz coordinates. -/
theorem proposition_14 {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μP : Measure Ω}
    (sys : System P Ω μP) (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂μP, Prop14Property sys T ω := by sorry

end UnknownLoads.Coxian
