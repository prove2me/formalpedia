-- Prove2me | Theorems.Thm_TaylorHGAudit_PEP_curvature_data
-- name    : TaylorHGAudit.PEP.curvature_data
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:49:39.028575+00:00
-- url     : https://prove2.me/theorems/dc6df73e-0946-4cbb-908f-6142adc6a69f
-- title:
--   Lemma 1 — curvature subtraction on full-class interpolation data
-- statement:
--   Let $(x_i,g_i,v_i)_{i\in I}$ be a finite family with $x_i,g_i\in\mathbb R^d$ and $v_i\in\mathbb R$, and let $0\le\mu<L\le+\infty$. Then
--
--   $$(x_i,g_i,v_i)_{i\in I}\text{ is }\mathcal F_{\mu,L}\text{-interpolable}
--   \quad\Longleftrightarrow\quad
--   \left(x_i,g_i-\mu x_i,v_i-\frac\mu2\|x_i\|^2\right)_{i\in I}
--   \text{ is }\mathcal F_{0,L-\mu}\text{-interpolable}.$$
--
--   Both interpolation predicates quantify over proper closed extended-valued functions. This is the data transformation accompanying Theorem 3, retaining both directions and the infinite-$L$ case.
--
--   Differences from the source:
--   - encoding: finite nonnegative curvature and extended positive smoothness on Euclidean space → NNReal curvature, ENNReal smoothness, EReal function values and real-height epigraph convexity; reason: the strict parameter hypothesis excludes zero smoothness and preserves every source instance, including infinite smoothness; only finite quadratic values are subtracted
--   - encoding: a finite set of triples with real values and Euclidean points and subgradients → an arbitrary Fintype index, EuclideanSpace vectors and HasOracle finite-value witnesses; reason: indexing permits repeated data and the empty family without changing the existence claim; witnesses range over the full extended-valued source class
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, Lemma 1, p. 9 (PDF 9), https://arxiv.org/abs/1502.05666v6

import Mathlib
import Definitions.Def_TaylorHGAudit_PEP_Class

namespace TaylorHGAudit.PEP

theorem curvature_data {d : ℕ} {ι : Type*} [Fintype ι]
    (μ : NNReal) (L : ENNReal) (hμL : (μ : ENNReal) < L)
    (x g : ι → E d) (v : ι → ℝ) :
    Interpolable μ L x g v ↔
      Interpolable 0 (L - (μ : ENNReal)) x
        (fun i => g i - (μ : ℝ) • x i)
        (fun i => v i - (μ : ℝ) / 2 * ‖x i‖ ^ 2) := by sorry

end TaylorHGAudit.PEP
