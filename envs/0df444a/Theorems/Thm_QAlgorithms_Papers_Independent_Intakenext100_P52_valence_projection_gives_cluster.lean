-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_valence_projection_gives_cluster
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.valence_projection_gives_cluster
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:47:28.634129+00:00
-- url     : https://prove2.me/theorems/5e9c7df9-9089-4c5b-b4b7-a609260e2a00
-- title:
--   Lemma 3: valence-bond projection gives the cluster
-- statement:
--   Let $G$ be an $r\times c$ rectangular grid in which every vertex is incident to an edge; nontrivial one-dimensional rows are included. Let $V=rc$, let $E$ be the number of grid edges, and prepare one normalized $H$-bond per edge, with one virtual qubit at each endpoint. At every vertex apply $\Pi_v=|0\rangle\langle0\cdots0|+|1\rangle\langle1\cdots1|$, and let $\Pi$ be their tensor product. Then
--
--   $$ \Pi|\mathrm{grid}\rangle=\gamma|C_G\rangle,\qquad\gamma=\frac{(\sqrt2)^V}{2^E}>0,\qquad\|\Pi|\mathrm{grid}\rangle\|=\gamma. $$
--
--   Thus the projected vector is nonzero and division by $\gamma$ gives precisely the normalized cluster state. The bond-only construction excludes an isolated physical site, for which the source supplies no degree-zero local-resource convention. The empty grid uses the scalar vacuum convention.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 17, Lemma 3: valence-bond projection gives the cluster

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Lemma 3, PDF p.17: rectangular grids, including nontrivial 1D rows.
Every site is incident to a bond, since the source's bond-only resource does
not specify a degree-zero local state. Nonzero norm is a conclusion.
The exact coefficient is (sqrt(2))^V / 2^E, so normalization is well-defined. -/
theorem valence_projection_gives_cluster (r c : ℕ)
    (hincident : ∀ v : RectangularSites r c, ∃ e ∈ gridEdges r c, e.1 = v ∨ e.2 = v) :
    let E := gridEdges r c
    let v := applyRect (valenceProjection E) (bondGrid E)
    let factor : ℝ := (Real.sqrt 2) ^ (r*c) / (2 : ℝ) ^ E.card
    v = (factor : ℂ) • graphClusterState E ∧ 0 < factor ∧ ‖v‖ = factor ∧
    v ≠ 0 ∧ ((factor : ℂ)⁻¹) • v = graphClusterState E := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
