-- Prove2me | Theorems.Thm_WeierstrassProjModel_nontrivial_chartTensor_of_isElliptic
-- name    : WeierstrassProjModel.nontrivial_chartTensor_of_isElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/5c78ddc2-dadf-5d09-b5e1-47052cb35b0d
-- title:
--   Nontriviality of the chart rings of E ×_R E
-- statement:
--   Let $R$ be a commutative ring which is in addition an integral domain and Noetherian, and let $W$ be a Weierstrass curve over $R$ satisfying `W.IsElliptic`. For an index $m \in \{0,1,2\}$ write $\mathcal{A}_m$ for the degree-zero homogeneous localisation `HomogeneousLocalization.Away` of the graded ring $R[X_0,X_1,X_2]/(F)$ at the image of $X_m$, where $F$ is the homogeneous Weierstrass cubic `W.toProjective.polynomial`, the ideal is the homogeneous ideal it spans, and the grading `projModelGradingCR` is the one obtained by pushing the homogeneous submodules of $R[X_0,X_1,X_2]$ forward along the quotient map; each $\mathcal{A}_m$ is an $R$-algebra through the composite of $R \to (\text{degree-}0\text{ part})$ with the canonical map to the localisation, as provided by `kw_pbac_awayAlgebra`. The assertion is that for every pair of indices $i, j \in \{0,1,2\}$ the tensor product $\mathcal{A}_i \otimes_R \mathcal{A}_j$ is a nontrivial ring, i.e. $0 \neq 1$ in it.
--
--   The nine rings $\mathcal{A}_i \otimes_R \mathcal{A}_j$ are the coordinate rings of the standard affine charts $D(\overline{X_i}) \times_R D(\overline{X_j})$ covering the fibre square $E \times_R E$ of the projective model $E$ of $W$; the statement says each such chart is nonempty. It supplies the nontriviality half of [`WeierstrassProjModel.isDomain_chartTensor_of_isElliptic`](thm.html#WeierstrassProjModel.isDomain_chartTensor_of_isElliptic), whose remaining half (absence of zero divisors) comes from integrality of the product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_nontrivial_chartTensor_of_isElliptic.lean

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

theorem WeierstrassProjModel.nontrivial_chartTensor_of_isElliptic
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i j : Fin 3) :
    Nontrivial ((𝒜 i) ⊗[R] (𝒜 j)) := by sorry
