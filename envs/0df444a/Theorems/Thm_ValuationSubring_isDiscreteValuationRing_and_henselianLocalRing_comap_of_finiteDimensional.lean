-- Prove2me | Theorems.Thm_ValuationSubring_isDiscreteValuationRing_and_henselianLocalRing_comap_of_finiteDimensional
-- name    : ValuationSubring.isDiscreteValuationRing_and_henselianLocalRing_comap_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/8d853b01-6131-5783-955c-4409aaa659b9
-- title:
--   Finite layers over a henselian discrete valuation subring
-- statement:
--   Let $F$ and $E$ be fields with $F$ of characteristic $0$, and let $E$ be an $F$-algebra. Let $A$ be a valuation subring of $E$, and let $k_0$ be an intermediate field of $E/F$. Write $A \cap k_0$ for the valuation subring `A.comap (algebraMap k₀ E)` of $k_0$, that is, the set of elements of $k_0$ whose image in $E$ lies in $A$. Assume that $A \cap k_0$ is a discrete valuation ring and that it is a henselian local ring. Let $K$ be an intermediate field of $E/k_0$ which is finite-dimensional as a $k_0$-vector space. The conclusion is that the valuation subring $A \cap K =$ `A.comap (algebraMap K E)` of $K$ is again both a discrete valuation ring and a henselian local ring. The case $K = k_0$ is included.
--
--   This is the standard statement that a henselian discrete valuation ring remains a henselian discrete valuation ring after passing to a finite extension of its fraction field, here in the form of pullbacks of a fixed valuation subring $A$ of a large ambient field $E$ along the finite layers $K/k_0$. It supplies the coefficient rings for the towers occurring in [`ModularCurve.FullLevel.exists_igusaTower_smoothPointData_of_stable`](thm.html#ModularCurve.FullLevel.exists_igusaTower_smoothPointData_of_stable) and in the Čerednik–Drinfel'd construction [`CerednikDrinfeld.QM.exists_intermediateField_abelianSchemePropertyBundle_isPullback_of_quaternionOrder_action_of_forall_isUnit_tensorProduct_padic`](thm.html#CerednikDrinfeld.QM.exists_intermediateField_abelianSchemePropertyBundle_isPullback_of_quaternionOrder_action_of_forall_isUnit_tensorProduct_padic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isDiscreteValuationRing_and_henselianLocalRing_comap_of_finiteDimensional.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.isDiscreteValuationRing_and_henselianLocalRing_comap_of_finiteDimensional
    {F E : Type} [Field F] [Field E] [CharZero F] [Algebra F E] (halg : Algebra.IsAlgebraic F E)
    (A : ValuationSubring E) (k₀ : IntermediateField F E)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ E)))
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ E)))
    (K : IntermediateField ↥k₀ E) (hK : FiniteDimensional ↥k₀ ↥K) :
    IsDiscreteValuationRing ↥(A.comap (algebraMap ↥K E)) ∧ HenselianLocalRing ↥(A.comap (algebraMap ↥K E)) := by sorry
