-- Prove2me | Theorems.Thm_PolyhedralPacking1261_Packing_Supplement_theorem_8
-- name    : PolyhedralPacking1261.Packing.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:43:14.454125+00:00
-- url     : https://prove2.me/theorems/6be60760-50a3-466e-ac4b-08953a5729ab
-- title:
--   Theorem 8 (Lower Bound) — a packable separated family of bc-parallelepipeds has at most $C_\varepsilon n^\varepsilon/(bc\tau)$ members
-- statement:
--   For every $\varepsilon>0$ there is a constant $C_\varepsilon>0$ such that the following holds. Let $b,c>0$ and let $\mathcal P$ be a family of at most $n$ bc-parallelepipeds (each with parameters $a_i>0$, $u_i,v_i\in\mathbb R$, $k_i\in\mathbb Z$ and fitting individually in the unit cube: $a_i+|u_i|+|v_i|\le1$, $(1+|k_i|)b\le1$, $c\le1$) that can be packed by translations into the unit cube. If for some $0<\tau\le2$ we have $d(P_i,P_j)=|u_i-u_j|+|v_i-v_j|>\tau$ for every pair of distinct objects with $k_i=k_j$, then
--
--   $$|\mathcal P|\ \le\ C_\varepsilon\,\frac{n^\varepsilon}{bc\tau}.$$
--
--   This geometric lower bound is the core of the paper's analysis: applied to one representative per component of the threshold graphs it bounds the total spanning-tree weight, and hence the optimum from below.
--
--   Differences from the source:
--   - encoding: a family P of at most n bc-parallelepipeds; |P| → parameter records P : Fin m → BCParameters with m ≤ n (repetitions kept), m the cardinality; n ∈ ℕ arbitrary, n^ε as a real power; reason: Lean convention for a finite indexed family; n = 0 forces the empty family, where the bound holds
--   - encoding: can be packed by translations into the unit cube → ∃ centers p with PackedInUnitCube b c P p (each p_i + P_i ⊆ [0,1]³, distinct ones with disjoint interiors); reason: the base mission's centered bcBody and ambient-interior convention
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, Theorem 8 (Lower Bound), §2.2, PDF p.10 (printed p.9); proof in §3, PDF pp.11–15 (printed pp.10–14)

import Definitions.Def_PolyhedralPacking1261_Packing_Supplement_SlopeGroups

set_option autoImplicit false

namespace PolyhedralPacking1261.Packing.Supplement

open PolyhedralPacking1261.Packing

/-- Theorem 8 (Lower Bound), PDF p.10 (printed p.9). For every `ε > 0` there is
`C_ε > 0` such that every family of at most `n` bc-parallelepipeds of one type
(`b, c > 0`, each fitting individually in the unit cube) that can be packed by
translations into the unit cube, and whose distinct members of equal shadow class are
at shear distance more than `τ` for some `0 < τ ≤ 2`, has at most `C_ε n^ε / (bcτ)`
members. -/
theorem theorem_8 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ) (b c τ : ℝ) (P : Fin m → BCParameters),
        0 < b → 0 < c → (∀ i, IndividuallyFits b c (P i)) → m ≤ n →
        (∃ p : Fin m → Point3, PackedInUnitCube b c P p) →
        0 < τ → τ ≤ 2 → SameShadowSeparated τ P →
        (m : ℝ) ≤ C * (n : ℝ) ^ ε / (b * c * τ) := by sorry

end PolyhedralPacking1261.Packing.Supplement
