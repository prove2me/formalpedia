-- Prove2me | Theorems.Thm_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
-- name    : ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/d0a402c9-07df-5865-86c2-03a7859c428c
-- title:
--   Gauss reduction of a q-expansion valuation ring
-- statement:
--   Let $L$ be a field, let $K$ be an intermediate field of the extension $L \subseteq L((q)) =$ `LaurentSeries L`, and let $A$ be a discrete valuation ring (a commutative domain with the `IsDiscreteValuationRing` structure) which is an $L$-algebra with $L$ as its fraction field, together with an $A$-algebra structure on $K$ compatible with that on $L$ via the scalar tower. Let $W_0$ be a valuation subring of $K$, and write $\bar{\ }$ for the coefficientwise reduction `IsLocalRing.residue A` of power series over $A$ to power series over the residue field $\kappa =$ `IsLocalRing.ResidueField A`. Assume: (i) an element $f \in K$ lies in $W_0$ if and only if there are $x, y \in A[[q]]$ with $\bar y \neq 0$ and $f \cdot y = x$ inside $L((q))$, the power series over $A$ being pushed to $L$ and embedded as Hahn series; (ii) for every $f \in K$ and every such presentation $f\cdot y = x$ with $\bar y \neq 0$, $f$ belongs to `W₀.nonunits` (the elements of valuation less than $1$) precisely when $\bar x = 0$. Then there exists a ring homomorphism $\mathrm{red} \colon W_0 \to \kappa((q))$ such that $\mathrm{red}(f) = \bar x / \bar y$ in $\kappa((q))$ for every $f \in W_0$ and every presentation $f \cdot y = x$ with $x, y \in A[[q]]$, $\bar y \neq 0$, and such that the kernel of $\mathrm{red}$ is the maximal ideal of the local ring $W_0$.
--
--   This is the Gauss reduction map attached to a valuation ring of $q$-expansions: reduction of a presentation $f = x/y$ with $x,y \in A[[q]]$ modulo the maximal ideal of $A$ is well defined, multiplicative and additive, and its kernel is the maximal ideal, so it identifies the residue field of $W_0$ with a subfield of $\kappa((q))$. It is the computational input for the determination of residue fields of Gauss valuations on function fields of modular curves read through $q$-expansions at the cusp $\infty$, and for the behaviour of such valuation rings under Atkin–Lehner involutions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hnu : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0)) :
    ∃ red : ↥W₀ →+* LaurentSeries (IsLocalRing.ResidueField A),
      (∀ (f : ↥W₀) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        ((f : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        red f = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))) ∧
      RingHom.ker red = IsLocalRing.maximalIdeal ↥W₀ := by sorry
