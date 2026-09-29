-- Prove2me | Theorems.Thm_TrivSqZeroExt_isLocalRing
-- name    : TrivSqZeroExt.isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/39ff7933-3051-5a0d-b067-de89073626e8
-- title:
--   Trivial square-zero extensions of local rings are local
-- statement:
--   Let $R$ be a commutative ring and $M$ an abelian group carrying compatible left and right $R$-module structures (a module over $R$ and over $R^{\mathrm{op}}$) whose two actions agree, i.e. the scalars are central. Suppose $R$ is a local ring, in Mathlib's sense: $R$ is nontrivial and its non-units form an ideal. Then the trivial square-zero extension $R \ltimes M = \mathrm{TrivSqZeroExt}\ R\ M$, that is the $R$-module $R \oplus M$ with multiplication $(r,m)(r',m') = (rr',\, r \cdot m' + m \cdot r')$ and unit $(1,0)$, is again a local ring. Taking $M = R$ this is the assertion that the ring of dual numbers $R[\varepsilon] = R[\varepsilon]/(\varepsilon^2)$ over a local ring is local.
--
--   The standard fact that adjoining a square-zero ideal to a local ring preserves locality, with the dual numbers $R[\varepsilon]$ as the case $M = R$. It is used in the treatment of first-order thickenings of schemes, where the local rings $\mathcal{O}_{X,x}[\varepsilon]$ must be recognised as local rings; in this development it is invoked in the construction of polarisations and of projective presentations of module sheaves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TrivSqZeroExt_isLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem TrivSqZeroExt.isLocalRing {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [IsLocalRing R] : IsLocalRing (TrivSqZeroExt R M) := by sorry
