-- Prove2me | Theorems.Thm_Rudin_ch07_stone_weierstrass
-- name    : Rudin.ch07_stone_weierstrass
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-13T00:56:29.139057+00:00
-- url     : https://prove2.me/theorems/fae71a7a-1cdf-40ce-a74a-b07280a44962
-- title:
--   Theorem 7.32 — Stone–Weierstrass
-- statement:
--   Let $\mathcal{A}$ be an algebra of real continuous functions on a compact set $K$. If $\mathcal{A}$ separates points on $K$ and vanishes at no point of $K$, then every real continuous function on $K$ lies in the uniform closure of $\mathcal{A}$: it is the uniform limit on $K$ of a sequence of members of $\mathcal{A}$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 7, p. 162, Theorems 7.29, 7.31 and 7.32

import Mathlib
import Definitions.Def_Rudin_ch07_families

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 7.32 (Stone–Weierstrass): let `A` be an algebra of real continuous functions
on a compact set `K`.  If `A` separates points on `K` and vanishes at no point of `K`, then
the uniform closure of `A` on `K` contains every function that is continuous on `K`. -/
theorem ch07_stone_weierstrass {X : Type*} [MetricSpace X] (K : Set X) (hK : IsCompact K)
    (A : Set (X → ℝ)) (halg : IsFunctionAlgebra A) (hcont : ∀ f ∈ A, ContinuousOn f K)
    (hsep : SeparatesPointsOn A K) (hvan : VanishesAtNoPointOn A K) :
    ∀ g : X → ℝ, ContinuousOn g K → g ∈ UniformClosureOn A K := by sorry

end Rudin
