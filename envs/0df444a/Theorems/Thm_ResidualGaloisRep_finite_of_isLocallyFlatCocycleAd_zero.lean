-- Prove2me | Theorems.Thm_ResidualGaloisRep_finite_of_isLocallyFlatCocycleAd_zero
-- name    : ResidualGaloisRep.finite_of_isLocallyFlatCocycleAd_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/875b6ea2-9ce9-593e-83fc-d8677f4a893c
-- title:
--   Finiteness of k from a finite flat trivial deformation
-- statement:
--   Let $k$ be a field, let $p$ be a prime, and let $\bar\rho$ be a residual Galois representation over $k$, i.e. a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\rho$ from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{End}_k V$ that factors through a finite level (there is a finite-dimensional intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$ such that every automorphism fixing $L$ pointwise is sent to $1$). Assume the predicate `IsLocallyFlatCocycleAd` holds for $p$ and for the zero $1$-cocycle of the restriction, along the map $\mathrm{Aut}_{\mathbb Q_p}(\overline{\mathbb Q}_p) \to \mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$, of the adjoint representation $\sigma \mapsto \rho(\sigma)\,\cdot\,\rho(\sigma)^{-1}$ on $\mathrm{End}_k V$: that is, there are a commutative ring $H$ carrying a Hopf algebra structure over $\mathbb Z_p$, finite and flat as a $\mathbb Z_p$-module and with cocommutative comultiplication, and a bijection $e$ from the convolution monoid of $\mathbb Z_p$-algebra maps $H \to \overline{\mathbb Q}_p$ onto $V \times V$ which carries the convolution product to addition and intertwines the Galois action on algebra maps ($g = \sigma \circ f$) with the diagonal action $(x_1,x_2) \mapsto (\rho(\sigma)x_1, \rho(\sigma)x_2)$ obtained from the zero cocycle. Then $k$ is finite.
--
--   This records that the finite flat condition at $p$ for the trivial first-order deformation of $\bar\rho|_{G_p}$ already forces the coefficient field to be finite, since the definition of `IsLocallyFlatCocycleAd` imposes no finiteness on $k$ itself. It is used in [`ResidualGaloisRep.exists_isLocallyFlatCocycleAd_smul_one`](thm.html#ResidualGaloisRep.exists_isLocallyFlatCocycleAd_smul_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_finite_of_isLocallyFlatCocycleAd_zero.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem ResidualGaloisRep.finite_of_isLocallyFlatCocycleAd_zero
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (hflat : ρbar.IsLocallyFlatCocycleAd p 0) : Finite k := by sorry
