-- Prove2me | Theorems.Thm_SocialEquilibrium_Existence_isContractible_prod
-- name    : SocialEquilibrium.Existence.isContractible_prod
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:40:52.680671+00:00
-- url     : https://prove2.me/theorems/9509ceb6-589e-40f6-97c8-bfbfcdb62bd0
-- title:
--   §1 — the product of two sets deformable into points is deformable into the pair
-- statement:
--   Let $E$ and $F$ be finite-dimensional real normed spaces (the paper's $\mathbb R^l$ and $\mathbb R^m$), and let $X\subseteq E$ and $Y\subseteq F$ be deformable into the points $x^0\in X$ and $y^0\in Y$ respectively. Then
--   $$X\times Y\subseteq E\times F\ \text{ is deformable into the point } (x^0,y^0).$$
--   In particular, the product of two contractible sets is contractible.
--
--   This is used to show that the set of action profiles and the values of the best-response map $\phi$ are contractible.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 888, §1 Topological Concepts (product of two contractible sets)

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsContractible

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §1, p. 888: the product of two sets `X ⊆ ℝˡ`, `Y ⊆ ℝᵐ` deformable into the
points `x⁰ ∈ X`, `y⁰ ∈ Y` respectively is deformable into the point `(x⁰, y⁰)`. -/
theorem isContractible_prod {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} (x₀ : X) (y₀ : Y)
    (hX : IsDeformableInto X x₀) (hY : IsDeformableInto Y y₀) :
    IsDeformableInto (X ×ˢ Y) ⟨(x₀.1, y₀.1), x₀.2, y₀.2⟩ := by sorry

end SocialEquilibrium.Existence
