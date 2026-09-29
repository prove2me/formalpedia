-- Prove2me | Theorems.Thm_ResidualGaloisRep_isLocallyFlatCocycleAd_add
-- name    : ResidualGaloisRep.isLocallyFlatCocycleAd_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/583e1aef-be64-56ac-817b-2a9809a4b03c
-- title:
--   Locally flat ad ρ̄-cocycles are closed under addition
-- statement:
--   Let $k$ be a field, let $p$ be a prime, and let $\bar\rho$ be a residual Galois representation over $k$: a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_k V$ which factors through a finite level, in the sense that some finite-dimensional intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$ has the property that every automorphism fixing $L$ pointwise is sent to $1$. Write $\Gamma_p$ for the group of $\mathbb Q_p$-algebra automorphisms of the chosen algebraic closure `PadicAlgCl p` of $\mathbb Q_p$, mapped to $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ by restriction of scalars to $\mathbb Q$ followed by restriction to $\overline{\mathbb Q}$. Let $c, c'$ be $1$-cocycles of $\Gamma_p$ with values in the restriction along this map of the adjoint representation $\sigma \mapsto \big(f \mapsto \rho(\sigma) \circ f \circ \rho(\sigma^{-1})\big)$ on $\mathrm{End}_k V$. Assume each of $c$ and $c'$ satisfies `IsLocallyFlatCocycleAd`, i.e. there is a commutative ring $H$ carrying a Hopf algebra structure over $\mathbb Z_p$, finite and flat as a $\mathbb Z_p$-module and with cocommutative comultiplication, and a bijection $e$ from the set $H \to_{\mathbb Z_p} \mathrm{PadicAlgCl}\,p$ of $\mathbb Z_p$-algebra maps, with its convolution multiplication, to $V \times V$ such that $e(fg) = e(f) + e(g)$ and such that for every $\sigma \in \Gamma_p$ and all $f, g$ with $g(h) = \sigma(f(h))$ for all $h \in H$ one has $e(g) = \big(\rho(\sigma)x_1,\, c(\sigma)(\rho(\sigma)x_1) + \rho(\sigma)x_2\big)$ where $(x_1,x_2) = e(f)$ (and likewise for $c'$). Then $c + c'$ also satisfies `IsLocallyFlatCocycleAd`.
--
--   This is the additivity half of the statement that the finite flat classes form a subgroup of $H^1(\mathbb Q_p, \mathrm{ad}\,\bar\rho)$: the dual-lift module attached to $c + c'$ is the Baer sum of those attached to $c$ and to $c'$, and finite flatness over $\mathbb Z_p$ is preserved by forming a tensor product of Hopf algebras, passing to the scheme-theoretic closure of a Galois-stable subgroup of points, and passing to a quotient. It is used in the construction of an injection from the locally flat classes at $p$ into the relevant self-extension group, via [`ResidualGaloisRep.exists_injective_localFlatClassesAd_selfExt_of_hondaSystem_model`](thm.html#ResidualGaloisRep.exists_injective_localFlatClassesAd_selfExt_of_hondaSystem_model).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_isLocallyFlatCocycleAd_add.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem ResidualGaloisRep.isLocallyFlatCocycleAd_add
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (c c' : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)))
    (hc : ρbar.IsLocallyFlatCocycleAd p c) (hc' : ρbar.IsLocallyFlatCocycleAd p c') :
    ρbar.IsLocallyFlatCocycleAd p (c + c') := by sorry
