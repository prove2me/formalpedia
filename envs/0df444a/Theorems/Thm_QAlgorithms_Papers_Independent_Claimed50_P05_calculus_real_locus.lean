-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_real_locus
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_real_locus
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:08:53.248688+00:00
-- url     : https://prove2.me/theorems/9deeeea8-038d-4653-baaa-6bb11d472e0c
-- title:
--   Corollary 4.4
-- statement:
--   Let $H$ be a complex Hilbert space and $\Phi$ a Borel calculus on $\mathbb C^d$. If $\Phi(z_j)$ is self-adjoint for every coordinate function $z_j$, then
--
--   $$\Phi\text{ is concentrated on }\mathbb R^d=\{z\in\mathbb C^d:\operatorname{Im}z_j=0\text{ for every }j\}.$$
--
--   The real locus uses the canonical embedding in $\mathbb C^d$.
--
--   This reduces complex base spaces when all coordinate images are self-adjoint.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 17, Corollary 4.4

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Corollary 4.4, PDF p.17: every self-graphAdjoint restrictedCoordinate forces concentration on the real locus. -/
theorem calculus_real_locus {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {d : ℕ} (F : Symbol (Fin d → ℂ) ℂ → Relation E) (hF : Calculus F)
    (h : ∀ j, SelfAdjoint (k := ℂ) (F (fullCoordinate j))) :
    Concentrated F {z | ∀ j, (z j).im = 0} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
