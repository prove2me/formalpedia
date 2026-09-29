-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_a2_exists_sixU_ne_zero_of_pointClass_ne
-- name    : WeierstrassProjModel.kw_a2_exists_sixU_ne_zero_of_pointClass_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/b5338b8c-443e-52cf-a5ad-b1206ce32774
-- title:
--   Non-vanishing of an addition-law element off the diagonal
-- statement:
--   Let $R$ be a commutative ring, $W$ a Weierstrass curve over $R$, and $F$ a field which is an $R$-algebra. For $i : \mathrm{Fin}\,3$ write $\mathcal A_i$ for the degree-zero homogeneous localisation `HomogeneousLocalization.Away` of the graded ring $\mathrm{MvPolynomial}(\mathrm{Fin}\,3, R)/(\,W_{\mathrm{proj}}\text{-polynomial}\,)$ — the grading being the image of the homogeneous-submodule grading under the quotient map, the ideal being the span of the projective Weierstrass polynomial of `W.toProjective` — at the image of the variable $X_i$, regarded as an $R$-algebra via the degree-zero part. Assume $\mathrm{algebraMap}_{R\to F}(\Delta_W) \neq 0$, fix $i, j$ and $R$-algebra homomorphisms $\psi_i : \mathcal A_i \to F$, $\psi_j : \mathcal A_j \to F$, and form the triples $\mathrm{kw\_lrApt\_chartEval}\,W\,F\,i\,\psi_i = (k \mapsto \psi_i(\mathrm{gen}\,i\,k)) \in F^{\mathrm{Fin}\,3}$ and likewise for $j$. Assume the two triples have distinct classes in `WeierstrassCurve.Projective.PointClass F`. Then some member of the family $\mathrm{kw\_lrSixU}\,W\,i\,j : \mathrm{Fin}\,3 \oplus \mathrm{Fin}\,3 \to \mathcal A_i \otimes_R \mathcal A_j$, whose left three entries are the chart-evaluated coordinates of the addition vector and whose right three entries are those of the symmetric addition vector, has nonzero image under $\mathrm{Algebra.TensorProduct.productMap}\,\psi_i\,\psi_j : \mathcal A_i \otimes_R \mathcal A_j \to F$.
--
--   This is the chord non-degeneracy step for the Lange–Ruppert system of two addition laws on the projective Weierstrass model: off the diagonal, at least one of the six tensor-product elements does not vanish at a given pair of chart points. It is used by [`WeierstrassProjModel.exists_lrSixU_ne_zero_xzcharts`](thm.html#WeierstrassProjModel.exists_lrSixU_ne_zero_xzcharts) and by [`WeierstrassProjModel.kw_a2_pin_map_mul_of_ne`](thm.html#WeierstrassProjModel.kw_a2_pin_map_mul_of_ne), and is the only place in those arguments where the hypothesis that the two point classes differ enters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_a2_exists_sixU_ne_zero_of_pointClass_ne.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

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
variable (F : Type u) [Field F] [Algebra R F]

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

theorem WeierstrassProjModel.kw_a2_exists_sixU_ne_zero_of_pointClass_ne
    (hΔ : algebraMap R F W.Δ ≠ 0) (i j : Fin 3)
    (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F)
    (hne : (⟦kw_lrApt_chartEval W F i ψᵢ⟧ : WeierstrassCurve.Projective.PointClass F)
           ≠ ⟦kw_lrApt_chartEval W F j ψⱼ⟧) :
    ∃ l, (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l) ≠ 0 := by sorry
