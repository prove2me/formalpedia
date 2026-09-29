-- Prove2me | Theorems.Thm_ValuationSubring_finsum_ramificationIdx_mul_inertiaDeg_eq_finrank
-- name    : ValuationSubring.finsum_ramificationIdx_mul_inertiaDeg_eq_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/9adebe71-7370-5a3a-a5ee-41b03900ae98
-- title:
--   Fundamental identity sum_B e(B∣ A)f(B∣ A)=[F:K]
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra that is finite-dimensional over $K$, let $A$ be a valuation subring of $K$ which is a discrete valuation ring, and assume that the integral closure of $A$ in $F$ is a finite $A$-module. Call a valuation subring $B$ of $F$ *over* $A$ if for every $x \in K$ one has $\mathrm{algebraMap}\,K\,F\,x \in B$ exactly when $x \in A$, i.e. $B \cap K = A$ inside $F$. The theorem asserts three things at once: first, the set of valuation subrings of $F$ over $A$ is finite; second, every valuation subring $B$ of $F$ over $A$ is itself a discrete valuation ring; and third, summing over the subtype of such $B$ — each equipped with the $A$-algebra structure obtained by corestricting the composite of $A \hookrightarrow K$ with $\mathrm{algebraMap}\,K\,F$ to $B$, which lands in $B$ precisely by the defining condition — the finsum of the products $e(\mathfrak m_B \mid \mathfrak m_A) \cdot f(\mathfrak m_B \mid \mathfrak m_A)$ of the ramification index `Ideal.ramificationIdx'` and the inertia degree `Ideal.inertiaDeg'` of the maximal ideal of $B$ over the maximal ideal of $A$ equals $\mathrm{finrank}_K F$. By the first clause the finsum is a genuine finite sum. No separability of $F/K$ and no hypothesis on characteristics or on the residue field are assumed.
--
--   This is the fundamental equality $\sum_{B} e(B\mid A) f(B\mid A) = [F:K]$ for the extensions of a discrete valuation of $K$ to a finite extension $F$, under the finiteness hypothesis on the integral closure that replaces separability. It is used in the project to enumerate the places of an algebraic curve lying over a given one and, in the level-one auxiliary analysis on modular curves, to identify the valuation subrings singled out by the Igusa valuation and to show that they are discrete valuation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_finsum_ramificationIdx_mul_inertiaDeg_eq_finrank.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.finsum_ramificationIdx_mul_inertiaDeg_eq_finrank
    {K F : Type*} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F]
    (A : ValuationSubring K) [IsDiscreteValuationRing A]
    [Module.Finite A (integralClosure A F)] :
    {B : ValuationSubring F | ∀ x : K, algebraMap K F x ∈ B ↔ x ∈ A}.Finite ∧
    (∀ B : ValuationSubring F, (∀ x : K, algebraMap K F x ∈ B ↔ x ∈ A) →
      IsDiscreteValuationRing B) ∧
    ∑ᶠ B : {B : ValuationSubring F // ∀ x : K, algebraMap K F x ∈ B ↔ x ∈ A},
      (letI : Algebra A B.1 := (((algebraMap K F).comp A.subtype).codRestrict B.1
          fun a => (B.2 a).mpr a.2).toAlgebra
       (IsLocalRing.maximalIdeal A).ramificationIdx' (IsLocalRing.maximalIdeal B.1) *
         (IsLocalRing.maximalIdeal A).inertiaDeg' (IsLocalRing.maximalIdeal B.1)) =
      Module.finrank K F := by sorry
