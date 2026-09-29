-- Prove2me | Theorems.Thm_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
-- name    : Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/5e946398-33e2-549e-b5a4-97f8ca85c2bb
-- title:
--   Krull–Akizuki theorem
-- statement:
--   Let $A$ be a commutative Noetherian integral domain of Krull dimension at most $1$ (`Ring.KrullDimLE 1 A`), let $K$ be a field which is an $A$-algebra and a fraction field of $A$, and let $L$ be a field equipped with an $A$-algebra and a $K$-algebra structure compatible as a scalar tower over $A \subseteq K \subseteq L$, with $L$ finite-dimensional as a $K$-vector space. Let $B$ be any $A$-subalgebra of $L$, that is, any subring of $L$ containing the image of $A$. The conclusion is the conjunction of three assertions: $B$ is a Noetherian ring; $B$ satisfies `Ring.DimensionLEOne`, i.e. every nonzero prime ideal of $B$ is maximal; and for every ideal $J$ of $B$ with $J \neq \bot$, the quotient $B / J$ is a module of finite length over $A$ (it admits a finite composition series as an $A$-module). No separability hypothesis on $L/K$ is imposed, and $B$ is not assumed integral over $A$ nor finitely generated as an $A$-algebra.
--
--   This is the Krull–Akizuki theorem together with its standard dimension and finite-length complements. It is used in the project to produce one-dimensional Noetherian rings, and in particular discrete valuation rings, inside finite and possibly inseparable extensions of the fraction field of a discrete valuation ring; the results on valuation subrings dominating a local ring and on intermediate fields with henselian local rings cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
    {A K L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L]
    (B : Subalgebra A L) :
    IsNoetherianRing B ∧ Ring.DimensionLEOne B ∧
      ∀ J : Ideal B, J ≠ ⊥ → IsFiniteLength A (B ⧸ J) := by sorry
