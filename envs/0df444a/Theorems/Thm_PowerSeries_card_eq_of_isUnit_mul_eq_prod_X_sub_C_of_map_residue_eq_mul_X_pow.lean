-- Prove2me | Theorems.Thm_PowerSeries_card_eq_of_isUnit_mul_eq_prod_X_sub_C_of_map_residue_eq_mul_X_pow
-- name    : PowerSeries.card_eq_of_isUnit_mul_eq_prod_X_sub_C_of_map_residue_eq_mul_X_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/8f961466-c836-5d50-bd0f-c9d7b1c0ba07
-- title:
--   Counting linear factors via reduction to unit· X^N
-- statement:
--   Let $T$ be a commutative local ring (in the sense of Mathlib's `IsLocalRing`), let $\iota$ be an arbitrary index type, let $S$ be a finite subset of $\iota$ and let $z : \iota \to T$ be a family of elements of $T$ such that $z_i$ lies in the maximal ideal of $T$ for every $i \in S$. Let $f, u$ be formal power series in one variable over $T$ with $u$ a unit in $T[\![X]\!]$, and let $N$ be a natural number. Assume two things: first, that the coefficientwise reduction of $f$ along the residue map $T \to T/\mathfrak{m} =$ `ResidueField T` is of the form $v \cdot X^N$ for some unit $v$ of $(T/\mathfrak{m})[\![X]\!]$; and second, that $u \cdot f = \prod_{i \in S} (X - C(z_i))$ in $T[\![X]\!]$, where $C$ denotes the constant-coefficient embedding. Then the cardinality of $S$ equals $N$. No injectivity of $z$ on $S$ is assumed, so the factors may repeat.
--
--   This is the degree-counting step which says that the number of linear factors $X - C(z_i)$ with $z_i$ topologically nilpotent modulo the maximal ideal is detected by the order of vanishing of the reduction of $f$. It is used in the construction of formal Drinfeld bases, being cited by [`WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.exists_reducesToOrigin_isDrinfeldBasisAdic_of_toPowerSeries_eq_typeZero`](thm.html#WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.exists_reducesToOrigin_isDrinfeldBasisAdic_of_toPowerSeries_eq_typeZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_card_eq_of_isUnit_mul_eq_prod_X_sub_C_of_map_residue_eq_mul_X_pow.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem PowerSeries.card_eq_of_isUnit_mul_eq_prod_X_sub_C_of_map_residue_eq_mul_X_pow
    {T : Type u} [CommRing T] [IsLocalRing T] {ι : Type*} (S : Finset ι) (z : ι → T)
    (hz : ∀ i ∈ S, z i ∈ maximalIdeal T) (f u : PowerSeries T) (hu : IsUnit u) (N : ℕ)
    (hf : ∃ v : PowerSeries (ResidueField T), IsUnit v ∧ PowerSeries.map (residue T) f = v * PowerSeries.X ^ N)
    (h : u * f = ∏ i ∈ S, (PowerSeries.X - PowerSeries.C (z i))) :
    S.card = N := by sorry
