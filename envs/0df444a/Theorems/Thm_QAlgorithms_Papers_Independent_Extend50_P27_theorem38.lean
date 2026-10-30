-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_theorem38
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.theorem38
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:00:47.741351+00:00
-- url     : https://prove2.me/theorems/a8d44fad-3f17-4c15-8511-bbfbeb5b000b
-- title:
--   Theorem 38: normalized power iteration converges
-- statement:
--   Let $A$ be a real matrix on a nonempty finite index set. Assume $A$ is symmetric positive semidefinite and primitive, including entrywise nonnegativity. Let $w^0_i>0$ and $\sum_iw^0_i=1$, and define
--
--   $$v^{m+1}=Aw^m,\qquad w^{m+1}=\frac{v^{m+1}}{\sum_jv^{m+1}_j}\quad(m\ge0).$$
--
--   Every output coordinate and normalization denominator is strictly positive. There is a positive sum-normalized Perron vector $x$, with $Ax=r(A)x$, and
--
--   $$\lim_{m\to\infty}w^m=x,\qquad\lim_{m\to\infty}\sum_jv^{m+1}_j=r(A)=\lambda_{\max}(A).$$
--
--   This gives convergence of both the approximate eigenvector and approximate spectral radius, with the source's sum normalization.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 27, Theorem 38: normalized power iteration converges

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Theorem 38, both convergence claims and well-definedness of every normalization
(PDF pp.27–28). PSD includes symmetry; primitive includes nonnegativity. The
printed r(M) is r(A), and v_(m+1) avoids the undefined initial v_0. -/
theorem theorem38 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (A : Matrix I I ℝ) (hPSD : A.PosSemidef) (hprimitive : A.IsPrimitive)
    (w0 : I → ℝ) (hw0pos : ∀ i, 0 < w0 i) (hw0sum : ∑ i, w0 i = 1) :
    ∃ x : I → ℝ,
      (∀ i, 0 < x i) ∧ (∑ i, x i) = 1 ∧ A *ᵥ x = topValue A • x ∧
      (spectralRadius ℝ A).toReal = topValue A ∧
      (∀ m, (∀ i, 0 < powerOutput A w0 m i) ∧ 0 < ∑ i, powerOutput A w0 m i) ∧
      Tendsto (powerIterate A w0) atTop (nhds x) ∧
      Tendsto (fun m => ∑ j, powerOutput A w0 m j) atTop (nhds (topValue A)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
