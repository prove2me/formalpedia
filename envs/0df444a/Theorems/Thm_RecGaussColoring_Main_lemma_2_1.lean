-- Prove2me | Theorems.Thm_RecGaussColoring_Main_lemma_2_1
-- name    : RecGaussColoring.Main.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:01.531349+00:00
-- url     : https://prove2.me/theorems/4aa11471-ee23-493f-af96-424c989e07f9
-- title:
--   Lemma 2.1 — projecting a cover
-- statement:
--   Let $X\subset\mathbb R^d$ be a finite $(s,\delta)$-cover of vectors of norm at most one, and let $z$ be a unit vector. For every $\varepsilon\ge0$, put $X^\perp=\{x-\langle x,z\rangle z:x\in X\}$. Then
--   $$
--   X^\perp\text{ is an }(s-\varepsilon,\delta-2\Phi^c(\varepsilon))\text{-cover}.
--   $$
--   This controls the loss from removing one direction. The statement allows every real $s$ and $\delta$; when the resulting lower bound is negative it remains a valid probability lower bound.
--
--   Differences from the source:
--   - encoding: finite Euclidean families and labelled finite graphs → Fin n vertices and EuclideanSpace ℝ (Fin d); reason: relabelling preserves every finite instance and dimension
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), Lemma 2.1, p. 7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Definitions.Def_RecGaussColoring_Main_Gaussian

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- Lemma 2.1, p. 7. -/
theorem lemma_2_1 (d : ℕ) (X : Finset (Space d)) (s δ : ℝ)
    (hcover : IsCover X s δ) (hnorm : ∀ x ∈ X, ‖x‖ ≤ 1)
    (z : Space d) (hz : ‖z‖ = 1) (ε : ℝ) (hε : 0 ≤ ε) :
  IsCover (X.image (projectOff z)) (s-ε) (δ-2*PhiTail ε) := by sorry

end RecGaussColoring.Main
