-- Prove2me | Theorems.Thm_ValuationSubring_toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian
-- name    : ValuationSubring.toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/ec63b326-1d13-5d85-a393-50b7c5eef009
-- title:
--   Unique extension of a henselian discrete valuation
-- statement:
--   Let $K$ and $F$ be fields with $F$ an algebra over $K$ that is finite-dimensional and separable as a $K$-algebra, and let $O$ be a valuation subring of $K$ which is a discrete valuation ring and a henselian local ring. Assume $F$ is also an $O$-algebra, compatibly with the $O$-algebra structure on $K$ and the $K$-algebra structure on $F$ (a scalar tower $O \to K \to F$). Let $O'$ be a valuation subring of $F$ lying over $O$, in the sense that for every $x \in K$ the image $\mathrm{algebraMap}_{K,F}(x)$ lies in $O'$ if and only if $x \in O$. The conclusion is threefold: first, $O'$ and the integral closure of $O$ in $F$ have the same underlying subring of $F$, i.e. $O'$ consists exactly of the elements of $F$ integral over $O$; second, that integral closure is a finite $O$-module; and third, it is a discrete valuation ring. Thus the valuation of $O$ admits a unique extension to $F$, namely the one given by the integral closure, which is module-finite over $O$ and again discrete.
--
--   This is the classical statement that a henselian discrete valuation extends uniquely to a finite separable extension, the extension being the integral closure, which is then a module-finite discrete valuation ring (Serre, Local Fields, II §2; Neukirch II §6, §8). It is used in the project to produce discrete valuation rings and henselian local rings by descent along finite separable extensions, to construct totally ramified layers, and in the analysis of smooth points of stalks after base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ValuationSubring.toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian
    {K F : Type} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] [HenselianLocalRing O]
    [Algebra O F] [IsScalarTower O K F]
    (O' : ValuationSubring F) (hO' : ∀ x : K, algebraMap K F x ∈ O' ↔ x ∈ O) :
    O'.toSubring = (integralClosure O F).toSubring ∧ Module.Finite O (integralClosure O F) ∧
      IsDiscreteValuationRing (integralClosure O F) := by sorry
