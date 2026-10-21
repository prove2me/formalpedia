-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_gordonMetric_curvature
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.gordonMetric_curvature
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:27:34.762374+00:00
-- url     : https://prove2.me/theorems/aafb16b0-7f77-4070-a034-507ee22fcced
-- title:
--   Scalar curvature and the continuity reduction
-- statement:
--   Let $c>0$ and constant $n\ge1$. Let $\mathbf u$ be $C^2$ on an open inertial Cartesian patch $D$ with $|\mathbf u|<c$, and put $U=\gamma(1,\mathbf u/c)$, $g=\eta+(n^{-2}-1)U_\flat U_\flat^T$, and $G=g^{-1}$. The actual scalar curvature $R$ of the Levi-Civita connection, using $R^a{}_{bcd}=\partial_c\Gamma^a_{bd}-\partial_d\Gamma^a_{bc}+\Gamma^a_{ec}\Gamma^e_{bd}-\Gamma^a_{ed}\Gamma^e_{bc}$ and $R=G^{bd}R^a{}_{bad}$, is
--
--   $$R=\frac{(n^2-1)^2}{2n^2}(U^\mu U^\nu-\eta^{\mu\nu})(\partial_\mu U^\iota)(\partial_\nu U_\iota)+\frac{1-n^4}{2n^2}(\partial_\mu U^\nu)(\partial_\nu U^\mu)+(1-n^2)\left[2U^\nu\partial_\nu(\partial_\mu U^\mu)+(\partial_\mu U^\mu)^2\right].$$
--
--   Indices run over the four spacetime coordinates, repeated indices are summed, and lowering on $U$ uses $\eta$. If $\partial_\mu U^\mu=0$ throughout $D$, the final bracket disappears.
--
--   The curvature is constructed from metric derivatives independently of this formula; the continuity assumption is needed only for the reduced expression.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 6, §III D, (52)–(54): scalar curvature and continuity reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.6, (52)–(54): actual Levi-Civita scalar curvature, and its reduction
when the four-divergence vanishes on the whole open coordinate patch. -/
theorem gordonMetric_curvature (c n : ℝ) (u : V4 → V3)
    (D : Set V4) (x : V4) (hc : 0 < c) (hn : 1 ≤ n)
    (hD : IsOpen D) (hx : x ∈ D) (hreg : ContDiffOn ℝ 2 u D)
    (hu : ∀ y ∈ D, dot3 (u y) (u y) < c ^ 2) :
    let U := fun y => fourFlow c (u y)
    let g := fun y => gDown c n (u y)
    let gi := fun y => gUp c n (u y)
    scalarCurvature g gi x = curvatureA n U x + curvatureB n U x + curvatureC n U x ∧
    ((∀ y ∈ D, divergence4 U y = 0) →
      scalarCurvature g gi x = curvatureA n U x + curvatureB n U x) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
