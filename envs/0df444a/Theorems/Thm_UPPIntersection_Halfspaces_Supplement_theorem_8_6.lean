-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_Supplement_theorem_8_6
-- name    : UPPIntersection.Halfspaces.Supplement.theorem_8_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:06:02.960658+00:00
-- url     : https://prove2.me/theorems/6ac98f83-d4f0-4151-a257-1168b9543f6b
-- title:
--   Theorem 8.6 — tightness of Theorem 7.2: $\mathrm{rank}_\pm(G\wedge G)\le2^{O(d\log\log N)}$ w.p. $1-o(1)$
-- statement:
--   For $N\ge d$, let $u_1,\dots,u_N,v_1,\dots,v_N$ be independent uniformly random points of the unit sphere $S^{d-1}$ and let $G_{i,j}=\operatorname{sgn}\langle u_i,v_j\rangle$. Then with probability $1-o(1)$,
--   $$\operatorname{rank}_\pm(G\wedge G)\le2^{O(d\log\log N)}.$$
--   In particular, the lower bound of Theorem 7.2 is tight up to a factor of $\log d$ in the exponent for $\lceil e^{Cd^2}\rceil\le N\le2^{d^{O(1)}}$.
--
--   Here $\log$ is base 2 and $G\wedge G$ is the disjoint conjunction of $G$ with itself.
--
--   **Formalization Note** The main clause is encoded with a universal $K>0$ and a function $\varepsilon(N)\to0$: for all $d\ge2$ and $N\ge d$, with probability at least $1-\varepsilon(N)$ every $\langle u_i,v_j\rangle\neq0$ and $\operatorname{rank}_\pm(G\wedge G)\le2^{Kd\log_2\log_2N}$. The error depends on $N$ only, so it is uniform in $d\le N$. The "in particular" clause is encoded as: there are $c,C>0$ such that for every exponent $A>0$ there are $K'>0$ and $\varepsilon'(d)\to0$ with $e^{cd}\le\operatorname{rank}_\pm(G\wedge G)\le2^{K'd\log_2d}$ with probability at least $1-\varepsilon'(d)$, uniformly over $\lceil e^{Cd^2}\rceil\le N\le2^{d^A}$.
--
--   Differences from the source:
--   - encoding: G_{i,j} = sgn⟨u_i,v_j⟩ as a ±1 sign matrix → a Bool matrix with true iff ⟨u_i,v_j⟩ > 0, and the event additionally requires every ⟨u_i,v_j⟩ ≠ 0; reason: the inner products are almost surely nonzero (p. 30), so adding this to the event does not change its probability and makes G a genuine sign matrix
--   - reading: with probability 1 − o(1) (asymptotic parameter not named) → probability at least 1 − ε(N) for all d ≥ 2 and N ≥ d, with ε(N) → 0 depending on N only; reason: N ≥ d makes N the natural asymptotic parameter; the error is taken uniform in d, which is the stronger reading and the one the proof gives (failure ≤ 2/(Nd)); d ≥ 2 is the sphere convention of p. 12
--   - encoding: 2^{O(d log log N)} → 2^{K d log₂ log₂ N} for one universal K > 0; reason: the O-constant is universal; log₂ log₂ N ≤ 0 only for N ≤ 2, where ε(N) may be ≥ 1
--   - encoding: the lower bound of Theorem 7.2 is tight up to a factor of log d in the exponent for ⌈e^{Cd²}⌉ ≤ N ≤ 2^{d^{O(1)}} → ∃ c, C > 0 ∀ A > 0 ∃ K' > 0, ε'(d) → 0: with probability ≥ 1 − ε'(d), e^{cd} ≤ rank_±(G∧G) ≤ 2^{K' d log₂ d}, uniformly over ⌈e^{Cd²}⌉ ≤ N ≤ 2^{d^A}; reason: this is the meaning of tightness: Theorem 7.2's lower bound e^{cd} against the upper bound 2^{O(d log d)} that holds on this range of N
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 33, Theorem 8.6 (proof on p. 33); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_SignRank
import Definitions.Def_UPPIntersection_Halfspaces_SignMatrices
import Definitions.Def_UPPIntersection_Halfspaces_Sphere
import Definitions.Def_UPPIntersection_Halfspaces_Supplement_Defs

open MeasureTheory Filter Topology SignRankMargin.OREquality

namespace UPPIntersection.Halfspaces.Supplement

/-- Bun–Juvekar, Theorem 8.6 (p. 33). For `N ≥ d` and independent uniform
`u₁, …, u_N, v₁, …, v_N ∈ S^{d-1}`, the matrix `G_{i,j} = sgn⟨u_i, v_j⟩` satisfies, with
probability `1 - o(1)`, `rank_±(G ∧ G) ≤ 2^{K d log₂ log₂ N}` for a universal `K > 0`
(i.e. `2^{O(d log log N)}`); the `o(1)` term depends on `N` only, so it is uniform in `d ≤ N`.
In particular the lower bound of Theorem 7.2 is tight up to a factor `log d` in the exponent for
`⌈e^{C d²}⌉ ≤ N ≤ 2^{d^{O(1)}}`: there are `c, C > 0` such that for every exponent `A > 0` there is
`K' > 0` with `e^{c d} ≤ rank_±(G ∧ G) ≤ 2^{K' d log₂ d}` with probability `1 - o(1)` as `d → ∞`,
uniformly over `⌈e^{C d²}⌉ ≤ N ≤ 2^{d^A}`. Both events include the almost-sure event that every
`⟨u_i, v_j⟩ ≠ 0`. -/
theorem theorem_8_6 :
    (∃ K : ℝ, 0 < K ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ d N : ℕ, 2 ≤ d → d ≤ N →
        1 - ε N ≤ ((sphereLawPow d N).prod (sphereLawPow d N)).real
          {p | (∀ i j, inner ℝ (p.1 i : EuclideanSpace ℝ (Fin d)) (p.2 j : EuclideanSpace ℝ (Fin d)) ≠ 0) ∧
            (signRank (andSquare (randSignMat p.1 p.2)) : ℝ) ≤
              (2 : ℝ) ^ (K * d * Real.logb 2 (Real.logb 2 N))}) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ A : ℝ, 0 < A → ∃ K' : ℝ, 0 < K' ∧
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ d N : ℕ, 2 ≤ d → ⌈Real.exp (C * (d : ℝ) ^ 2)⌉₊ ≤ N → (N : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) ^ A) →
        1 - ε d ≤ ((sphereLawPow d N).prod (sphereLawPow d N)).real
          {p | (∀ i j, inner ℝ (p.1 i : EuclideanSpace ℝ (Fin d)) (p.2 j : EuclideanSpace ℝ (Fin d)) ≠ 0) ∧
            Real.exp (c * d) ≤ (signRank (andSquare (randSignMat p.1 p.2)) : ℝ) ∧
            (signRank (andSquare (randSignMat p.1 p.2)) : ℝ) ≤
              (2 : ℝ) ^ (K' * d * Real.logb 2 d)}) := by sorry

end UPPIntersection.Halfspaces.Supplement
