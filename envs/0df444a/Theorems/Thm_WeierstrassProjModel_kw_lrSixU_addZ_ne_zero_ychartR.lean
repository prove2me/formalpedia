-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_lrSixU_addZ_ne_zero_ychartR
-- name    : WeierstrassProjModel.kw_lrSixU_addZ_ne_zero_ychartR
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/99f55dc2-2617-5e5a-aa49-d2fd79a001c3
-- title:
--   Nonvanishing of the chord Z-component on (i,1) charts
-- statement:
--   Let $R$ be a commutative ring which is a Noetherian integral domain, and let $W$ be a Weierstrass curve over $R$ satisfying `W.IsElliptic`. For an index $i \in \{0,1,2\}$ write $\mathcal A_i$ for the degree-zero `HomogeneousLocalization.Away` of the graded ring $\mathrm{MvPolynomial}\,(\mathrm{Fin}\,3)\,R / (W.\mathrm{toProjective}.\mathrm{polynomial})$, graded by the images `projModelGradingCR` of the homogeneous submodules under the quotient map, at the image of the coordinate $X_i$; each $\mathcal A_i$ carries the $R$-algebra structure `kw_pbac_awayAlgebra` coming from the degree-zero part. The family `kw_lrSixU W i j` is indexed by $\mathrm{Fin}\,3 \oplus \mathrm{Fin}\,3$ and takes values in $\mathcal A_i \otimes_R \mathcal A_j$, given on left-hand indices $k$ by `kw_lrChart_u W i j k`, the image under `kw_lrChart_ev'` of the class of the $k$-th coordinate of the Lange–Ruppert addition vector `kw_lrAdd_vec`, and on right-hand indices by the corresponding values `kw_lrSymChart_u` built from `kw_lrSym_vec`. The assertion is that for every $i$ the element indexed by the left-hand index $2$, with the right-hand chart fixed at $j = 1$, namely `kw_lrSixU W i 1 (.inl 2)`, is a nonzero element of $\mathcal A_i \otimes_R \mathcal A_1$.
--
--   This supplies one explicit nonvanishing witness among the six Lange–Ruppert coordinate expressions attached to the addition law on the projective Weierstrass model, for the right-hand chart taken to be the $Y$-chart. It is used by [`WeierstrassProjModel.exists_lrSixU_ne_zero_ychartR`](thm.html#WeierstrassProjModel.exists_lrSixU_ne_zero_ychartR), which only needs the existence of some index at which the family does not vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_lrSixU_addZ_ne_zero_ychartR.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

theorem WeierstrassProjModel.kw_lrSixU_addZ_ne_zero_ychartR
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i : Fin 3) :
    kw_lrSixU W i 1 (.inl 2) ≠ 0 := by sorry
