-- Prove2me | Theorems.Thm_PDivisibleGroup_Hopf_nsmulAlgHom_sub_nsmul_mem_augIdeal_sq
-- name    : PDivisibleGroup.Hopf.nsmulAlgHom_sub_nsmul_mem_augIdeal_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/ae9423c9-eb45-5d7d-a532-1d5150994b63
-- title:
--   Multiplication by n acts as n on I/I²
-- statement:
--   Let $R$ be a commutative ring and $A$ a commutative ring carrying the structure of an $R$-bialgebra, with counit $\varepsilon =$ `counitAlgHom R A` and augmentation ideal `augIdeal R A` $= \ker\varepsilon \subseteq A$. For a natural number $n$, `nsmulAlgHom R A n` denotes the $R$-algebra endomorphism of $A$ obtained as the $n$-th power of the identity algebra map in the convolution monoid on $\operatorname{Hom}_{R\text{-alg}}(A,A)$ (formed in the `WithConv` type synonym and transported back to an algebra map), i.e. the comorphism of multiplication by $n$ on the affine monoid scheme $\operatorname{Spec} A$. The assertion is that for every $x$ lying in the augmentation ideal, the difference
--   $$\mathrm{nsmulAlgHom}\,R\,A\,n\,(x) - n\cdot x$$
--   lies in the square $(\ker\varepsilon)^2$ of the augmentation ideal, where $n\cdot x$ is the $n$-fold sum $x+\dots+x$. No antipode, cocommutativity, finiteness or freeness hypothesis on $A$ is imposed, and $n = 0$ is allowed.
--
--   This is the infinitesimal statement that multiplication by $n$ on a commutative affine monoid (in particular group) scheme induces multiplication by $n$ on the cotangent space $I/I^2$ at the unit section, hence on invariant differentials and on the Lie algebra. In the present development it underlies the analysis of the torsion ideals `torsionIdeal R A n` = images of the augmentation ideal under `nsmulAlgHom`, which define the transition maps in a $p$-divisible group, and it is used in the study of Cartier duality and of the points and coordinates of the levels of such a tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_Hopf_nsmulAlgHom_sub_nsmul_mem_augIdeal_sq.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem PDivisibleGroup.Hopf.nsmulAlgHom_sub_nsmul_mem_augIdeal_sq
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A]
    (n : ℕ) {x : A} (hx : x ∈ PDivisibleGroup.Hopf.augIdeal R A) :
    PDivisibleGroup.Hopf.nsmulAlgHom R A n x - n • x ∈ PDivisibleGroup.Hopf.augIdeal R A ^ 2 := by sorry
