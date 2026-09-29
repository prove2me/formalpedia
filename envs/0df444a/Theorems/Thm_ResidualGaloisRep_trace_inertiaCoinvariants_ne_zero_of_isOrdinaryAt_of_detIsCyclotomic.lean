-- Prove2me | Theorems.Thm_ResidualGaloisRep_trace_inertiaCoinvariants_ne_zero_of_isOrdinaryAt_of_detIsCyclotomic
-- name    : ResidualGaloisRep.trace_inertiaCoinvariants_ne_zero_of_isOrdinaryAt_of_detIsCyclotomic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/28837cf6-541f-569e-bf41-8753cfb457bb
-- title:
--   Non-zero trace on inertia coinvariants of ordinary residual representations
-- statement:
--   Let $k$ be a field and $p$ an odd prime, and let $\bar\rho$ be a residual Galois representation over $k$: a $k$-vector space $V$ with $\operatorname{finrank}_k V = 2$ together with a monoid homomorphism $\bar\rho$ from $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q) = \mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\operatorname{End}_k V$ which is trivial on the subgroup fixing some finite-dimensional intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$. Assume, for the associated adic representation over $k$, the conditions `DetIsCyclotomic` at $p$ (namely $p = 0$ in $k$, and for every $n$, every $\sigma$ and every natural number $a$ such that $\sigma\mu = \mu^{a}$ for all $p^{n}$-th roots of unity $\mu$, one has $\det\bar\rho(\sigma) - a \in (p^{n}) \subseteq k$) and `IsOrdinaryAt` $p$ (for every valuation subring $P$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $P$ there is a submodule of $V$ spanned by the first vector of some basis, stable under the decomposition subgroup of $P$ over $\mathbb Q$, and containing $\bar\rho(\tau)v - v$ for all $\tau$ in the inertia subgroup of $P$, viewed inside the Galois group, and all $v \in V$). Fix such a $P$, an element $\sigma$ of the Galois group, and a $k$-linear endomorphism $E$ of the quotient of $V$ by $W := \sum_{\tau \in I_P} \operatorname{im}(\bar\rho(\tau) - 1)$ satisfying $E(v \bmod W) = \bar\rho(\sigma)v \bmod W$ for all $v \in V$. Then $\operatorname{tr}_k E \neq 0$.
--
--   This is the statement that the trace of $\bar\rho(\sigma)$ on the inertia coinvariants at $p$ of an odd ordinary residual representation with cyclotomic determinant is non-zero, the coinvariants being one-dimensional; classically it records the non-vanishing of the unramified quotient character at $\sigma$. It is used in the local Hecke-algebra arguments about ordinary families, in particular in the identification of Hecke operators at $p$ and in reducedness and irreducibility arguments for the associated Hecke rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_trace_inertiaCoinvariants_ne_zero_of_isOrdinaryAt_of_detIsCyclotomic.lean

import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.LinearAlgebra.Trace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ResidualGaloisRep.trace_inertiaCoinvariants_ne_zero_of_isOrdinaryAt_of_detIsCyclotomic
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρbar : ResidualGaloisRep k)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p)
    (hord : (GaloisRepAdic.ofResidualGaloisRep ρbar).IsOrdinaryAt p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (E : (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)) →ₗ[k]
      (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)))
    (hE : ∀ v : ρbar.V, E (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρbar.ρ σ v)) :
    LinearMap.trace k _ E ≠ 0 := by sorry
