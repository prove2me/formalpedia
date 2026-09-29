-- Prove2me | Theorems.Thm_Representation_injective_liftBaseChange_of_isAbsolutelyIrreducible
-- name    : Representation.injective_liftBaseChange_of_isAbsolutelyIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/e2c6bea8-b649-5d99-9879-4a648742c0d4
-- title:
--   Injectivity after base change for absolutely irreducible ρ
-- statement:
--   Let $F$ and $k$ be fields with $k$ an $F$-algebra, let $G$ be a group, let $V$ be an $F$-vector space, and let $W$ be a $k$-vector space equipped additionally with the compatible $F$-module structure given by the scalar tower $F \subseteq k$. Let $\rho$ be a representation of $G$ on $V$ over $F$ which is absolutely irreducible in the sense of the project predicate [`Representation.IsAbsolutelyIrreducible`](def/Representation_AbsolutelyIrreducible.html#L27) at universe level $0$: for every field $k'$ in `Type` carrying an $F$-algebra structure, the base-changed representation $k' \otimes_F \rho$ is irreducible. Let $\tau$ be a representation of $G$ on $W$ over $k$, and let $\iota : V \to W$ be an injective $F$-linear map which is $G$-equivariant, i.e. $\iota(\rho(g)v) = \tau(g)(\iota v)$ for all $g \in G$ and $v \in V$. Then the $k$-linear map $k \otimes_F V \to W$ obtained from $\iota$ by extension of scalars, `ι.liftBaseChange k`, is again injective.
--
--   This is the standard fact that an injective equivariant map out of an absolutely irreducible representation remains injective after extending scalars to the field of definition of the target, obtained from Schur-type dichotomy for the irreducible base change $k \otimes_F \rho$. It is used in the construction of Hecke eigensystems on cohomology, in [`HeckeEis.isEigensystemH1_of_H1_gammaH_dual_of_isCuspidalOfType_of_qCoeff_congr`](thm.html#HeckeEis.isEigensystemH1_of_H1_gammaH_dual_of_isCuspidalOfType_of_qCoeff_congr).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_injective_liftBaseChange_of_isAbsolutelyIrreducible.lean

import Definitions.Def_Representation_AbsolutelyIrreducible

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Representation.injective_liftBaseChange_of_isAbsolutelyIrreducible
    {F k G V W : Type} [Field F] [Field k] [Algebra F k] [Group G]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module k W] [Module F W] [IsScalarTower F k W]
    (ρ : Representation F G V) [Representation.IsAbsolutelyIrreducible.{0} ρ]
    (τ : Representation k G W)
    (ι : V →ₗ[F] W) (hι : Function.Injective ι)
    (hιG : ∀ (g : G) (v : V), ι (ρ g v) = τ g (ι v)) :
    Function.Injective (ι.liftBaseChange k) := by sorry
