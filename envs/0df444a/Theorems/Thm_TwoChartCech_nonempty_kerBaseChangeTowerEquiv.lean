-- Prove2me | Theorems.Thm_TwoChartCech_nonempty_kerBaseChangeTowerEquiv
-- name    : TwoChartCech.nonempty_kerBaseChangeTowerEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/82017eb7-6d2a-53dc-910d-a0eb15fcedd4
-- title:
--   Transitivity of base change on kernels of a linear map
-- statement:
--   Let $R$ be a commutative ring, let $C^0$ and $C^1$ be $R$-modules and let $d \colon C^0 \to C^1$ be $R$-linear. Let $S$ and $T$ be commutative rings, each an $R$-algebra, with $T$ an $S$-algebra and the scalar actions forming a tower over $R$ (all objects in a single universe). The assertion is that there exists a $T$-linear isomorphism
--   $$e \colon \ker\bigl((d \otimes_R S) \otimes_S T\bigr) \xrightarrow{\ \sim\ } \ker\bigl(d \otimes_R T\bigr),$$
--   where $d \otimes_R S \colon S \otimes_R C^0 \to S \otimes_R C^1$ is the base change of $d$ along $R \to S$ and $(d \otimes_R S) \otimes_S T$ its further base change along $S \to T$, such that for every $z$ in the source kernel the image $e(z)$, viewed as an element of $T \otimes_R C^0$, is the value at $z$ of the canonical cancellation isomorphism $T \otimes_S (S \otimes_R C^0) \cong T \otimes_R C^0$. Thus the isomorphism is not merely abstract: it is the restriction of the canonical comparison map to the kernels.
--
--   This is the transitivity (associativity) of extension of scalars, in the form needed for two-term complexes: the canonical isomorphism $T \otimes_S (S \otimes_R C^i) \cong T \otimes_R C^i$ carries $(d \otimes_R S) \otimes_S T$ to $d \otimes_R T$ and hence identifies their kernels. It is used in the bookkeeping for families of two-term complexes over a base, where restricting from an open subset to a smaller one and then to a point must agree with restricting to the point directly; it is cited by [`TwoChartCech.exists_fibreH0Family`](thm.html#TwoChartCech.exists_fibreH0Family).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_nonempty_kerBaseChangeTowerEquiv.lean

import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct

theorem TwoChartCech.nonempty_kerBaseChangeTowerEquiv
    {R : Type u} [CommRing R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] :
    ∃ e : LinearMap.ker ((d.baseChange S).baseChange T) ≃ₗ[T] LinearMap.ker (d.baseChange T),
      ∀ z, (e z : T ⊗[R] C0) = TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T C0 z := by sorry
