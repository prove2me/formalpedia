-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_Supplement_theorem_7_2
-- name    : UPPIntersection.Halfspaces.Supplement.theorem_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:02:55.797323+00:00
-- url     : https://prove2.me/theorems/68a6bc62-6265-4bcb-89ec-1a5d2f2da900
-- title:
--   Theorem 7.2 — random sphere sign matrix: $\mathrm{rank}_\pm(G)\le d$ and $\mathrm{rank}_\pm(G\wedge G)\ge e^{cd}$ w.p. $1-o(1)$
-- statement:
--   There are constants $c,C>0$ such that the following holds. Let $N=\lceil e^{Cd^2}\rceil$, let $u_1,\dots,u_N,v_1,\dots,v_N$ be independent uniformly random points of $S^{d-1}$, and let $G_{i,j}=\operatorname{sgn}\langle u_i,v_j\rangle$. Then with probability $1-o(1)$ as $d\to\infty$,
--   $$\operatorname{rank}_\pm(G)\le d\qquad\text{whereas}\qquad\operatorname{rank}_\pm(G\wedge G)\ge e^{cd}.$$
--   Here $G\wedge G$ is the disjoint conjunction with rows $(i_1,i_2)$, columns $(j_1,j_2)$ and entry $G_{i_1,j_1}\wedge G_{i_2,j_2}$, and both bounds hold on the same event.
--
--   This gives a second explicit family, besides bounded integer halfspaces, whose sign rank is small but whose disjoint conjunction has exponential sign rank.
--
--   **Formalization Note** $1-o(1)$ is encoded as: there is a function $\varepsilon(d)\to0$ with probability at least $1-\varepsilon(d)$ for every $d\ge2$.
--
--   Differences from the source:
--   - encoding: G_{i,j} = sgn⟨u_i,v_j⟩ as a ±1 sign matrix → a Bool matrix with true iff ⟨u_i,v_j⟩ > 0, and the event additionally requires every ⟨u_i,v_j⟩ ≠ 0; reason: the inner products are almost surely nonzero (p. 30), so adding this to the event does not change its probability and makes G a genuine sign matrix
--   - encoding: with probability 1 − o(1) → probability at least 1 − ε(d) for every d ≥ 2, for some ε(d) → 0 as d → ∞; reason: N is a function of d, so d is the only asymptotic parameter; d ≥ 2 is the paper's sphere convention (p. 12)
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 30, Theorem 7.2 (proof on p. 30); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_SignRank
import Definitions.Def_UPPIntersection_Halfspaces_SignMatrices
import Definitions.Def_UPPIntersection_Halfspaces_Sphere
import Definitions.Def_UPPIntersection_Halfspaces_Supplement_Defs

open MeasureTheory Filter Topology SignRankMargin.OREquality

namespace UPPIntersection.Halfspaces.Supplement

/-- Bun–Juvekar, Theorem 7.2 (p. 30). There are constants `c, C > 0` such that, for
`N = ⌈e^{C d²}⌉` and independent uniform `u₁, …, u_N, v₁, …, v_N ∈ S^{d-1}`, the matrix
`G_{i,j} = sgn⟨u_i, v_j⟩` satisfies, with probability `1 - o(1)` as `d → ∞`, both
`rank_±(G) ≤ d` and `rank_±(G ∧ G) ≥ e^{c d}` (together with the almost-sure event that every
`⟨u_i, v_j⟩ ≠ 0`, so that `G` is a sign matrix). -/
theorem theorem_7_2 : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ d : ℕ, 2 ≤ d →
      1 - ε d ≤
        ((sphereLawPow d ⌈Real.exp (C * (d : ℝ) ^ 2)⌉₊).prod
            (sphereLawPow d ⌈Real.exp (C * (d : ℝ) ^ 2)⌉₊)).real
          {p | (∀ i j, inner ℝ (p.1 i : EuclideanSpace ℝ (Fin d)) (p.2 j : EuclideanSpace ℝ (Fin d)) ≠ 0) ∧
            signRank (randSignMat p.1 p.2) ≤ d ∧
            Real.exp (c * d) ≤ (signRank (andSquare (randSignMat p.1 p.2)) : ℝ)} := by sorry

end UPPIntersection.Halfspaces.Supplement
