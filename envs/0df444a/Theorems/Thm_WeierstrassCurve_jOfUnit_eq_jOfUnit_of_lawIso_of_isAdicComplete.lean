-- Prove2me | Theorems.Thm_WeierstrassCurve_jOfUnit_eq_jOfUnit_of_lawIso_of_isAdicComplete
-- name    : WeierstrassCurve.jOfUnit_eq_jOfUnit_of_lawIso_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/66af7823-5b77-5606-b3ac-1042a5343bcb
-- title:
--   Serre–Tate: ⋆-isomorphic formal groups force equal j-invariants
-- statement:
--   Let $q$ be a prime with $q \neq 2$, let $k$ be a field of characteristic $q$, and let $E_0$ be an elliptic Weierstrass curve over $k$ whose formal group law satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`: taken with respect to the zero ideal of $k$, there is a unit power series $u$ with the $q$-th series `nthSeries q` of $E_0.\mathrm{formalGroup}$ equal to $u$ times its Drinfeld divisor `drinfeldDivisor q 0 0` (the supersingularity hypothesis). Let $T$ be a Noetherian local ring, complete for the adic filtration of its maximal ideal, and $\mathrm{res}_T : T \to k$ a surjective ring homomorphism whose kernel is the maximal ideal of $T$. Let $E, E'$ be Weierstrass curves over $T$ whose base changes along $\mathrm{res}_T$ both equal $E_0$, with discriminants $\Delta_E$ and $\Delta_{E'}$ units. Let $G, G'$ be formal group laws over $T$ whose underlying two-variable power series are the fixed Weierstrass group laws `formalGroupLawFixed` of $E$ and of $E'$ respectively, and let $\psi$ be an isomorphism $G \to G'$ of formal group laws, i.e. a power series with zero constant term and unit linear coefficient satisfying the homomorphism identity, such that $\mathrm{res}_T$ of the $n$-th coefficient of $\psi$ is $1$ for $n = 1$ and $0$ otherwise. Then the $j$-invariants `jOfUnit` of $E$ and $E'$, formed from the two unit-discriminant witnesses, are equal in $T$.
--
--   This is the $j$-invariant form of the Serre–Tate theorem on local moduli of a supersingular elliptic curve: over a complete local base, a deformation of the curve is determined, up to its $j$-invariant, by its formal group together with an isomorphism reducing to the identity. It feeds the supersingular deformation computations used in [`ModularCurve.LevelModuliPackageAbs.exists_coeff_nthSeries_sub_mul_mem_span_and_map_j0_sub_algebraMap_eq_mul_pow_of_factorsThrough_of_five_le_gamma0Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.exists_coeff_nthSeries_sub_mul_mem_span_and_map_j0_sub_algebraMap_eq_mul_pow_of_factorsThrough_of_five_le_gamma0Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_jOfUnit_eq_jOfUnit_of_lawIso_of_isAdicComplete.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem WeierstrassCurve.jOfUnit_eq_jOfUnit_of_lawIso_of_isAdicComplete
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (E E' : WeierstrassCurve T) (hE : E.map resT = E₀) (hE' : E'.map resT = E₀)
    (hΔ : IsUnit E.Δ) (hΔ' : IsUnit E'.Δ)
    (G : FormalGroup T) (hG : G.toPowerSeries = E.formalGroupLawFixed)
    (G' : FormalGroup T) (hG' : G'.toPowerSeries = E'.formalGroupLawFixed)
    (ψ : FormalGroup.LawIso G G')
    (hψ : ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) :
    E.jOfUnit hΔ = E'.jOfUnit hΔ' := by sorry
