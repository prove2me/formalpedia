-- Prove2me | Theorems.Thm_TwoChartCech_GrothendieckComplex_nonempty_of_isLocalRing
-- name    : TwoChartCech.GrothendieckComplex.nonempty_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/0bb75e28-d052-58d5-ae0e-3fe2e7cf9b6c
-- title:
--   Existence of a Grothendieck complex over a Noetherian local ring
-- statement:
--   Let $R$ be a commutative Noetherian local ring, let $C^0$ and $C^1$ be $R$-modules in the same universe as $R$, both flat over $R$, and let $d\colon C^0\to C^1$ be an $R$-linear map whose kernel $\ker d$ and whose cokernel, presented as the quotient $C^1/\operatorname{range} d$, are finitely generated $R$-modules. The assertion is that the type [`TwoChartCech.GrothendieckComplex d`](def/AlgebraicGeometry_TwoChartCech.html#L173) is nonempty, i.e. that there exist: a two-term complex $G$ consisting of two finitely generated free $R$-modules $G^0,G^1$ together with an $R$-linear differential $d_G\colon G^0\to G^1$; and $R$-linear maps $\iota_0\colon G^0\to C^0$, $\iota_1\colon G^1\to C^1$ with $d\circ\iota_0=\iota_1\circ d_G$, such that for every commutative $R$-algebra $A$ (again in the same universe) the two maps induced by base change along $R\to A$ are bijective: the $A$-linear map $\ker(d_G\otimes_R A)\to\ker(d\otimes_R A)$ obtained by restricting $\iota_0\otimes_R A$, and the $A$-linear map $(A\otimes_R G^1)/\operatorname{range}(d_G\otimes_R A)\to (A\otimes_R C^1)/\operatorname{range}(d\otimes_R A)$ induced by $\iota_1\otimes_R A$ on quotients. Only existence is asserted; no uniqueness or minimality statement is made.
--
--   This is the two-term case of the existence of a Grothendieck complex: a finite free complex computing the kernel and cokernel of a flat two-term complex compatibly with arbitrary base change, as in Hartshorne III.12.2 and Mumford's lemma on complexes computing cohomology. It is used in the treatment of cohomology and Riemann–Roch for smooth proper curves presented by a two-chart affine cover, where it is applied to the Čech differential of a flat coherent sheaf.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_GrothendieckComplex_nonempty_of_isLocalRing.lean

import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct

theorem TwoChartCech.GrothendieckComplex.nonempty_of_isLocalRing {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Nonempty (TwoChartCech.GrothendieckComplex d) := by sorry
