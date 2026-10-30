-- Prove2me | Theorems.Thm_TaylorHGAudit_PEP_conjugate_data
-- name    : TaylorHGAudit.PEP.conjugate_data
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:52:02.149919+00:00
-- url     : https://prove2.me/theorems/a1b25fe3-5a43-48fa-a8c5-d658b611df19
-- title:
--   Lemma 2 — conjugation on full-class interpolation data
-- statement:
--   Let $(x_i,g_i,v_i)_{i\in I}$ be a finite family in $\mathbb R^d\times\mathbb R^d\times\mathbb R$, and let $0<L\le+\infty$. Then
--
--   $$(x_i,g_i,v_i)_{i\in I}\text{ is }\mathcal F_{0,L}\text{-interpolable}
--   \quad\Longleftrightarrow\quad
--   (g_i,x_i,\langle x_i,g_i\rangle-v_i)_{i\in I}
--   \text{ is }\mathcal F_{1/L,+\infty}\text{-interpolable}.$$
--
--   Both sides allow the complete proper closed extended-valued function class, including infinite-$L$ interpolants. The equivalence exchanges points and subgradients and transforms their finite values.
--
--   Differences from the source:
--   - encoding: finite nonnegative curvature and extended positive smoothness on Euclidean space → NNReal curvature, ENNReal smoothness, EReal function values and real-height epigraph convexity; reason: the strict parameter hypothesis excludes zero smoothness and preserves every source instance, including infinite smoothness; only finite quadratic values are subtracted
--   - encoding: a finite set of triples with real values and Euclidean points and subgradients → an arbitrary Fintype index, EuclideanSpace vectors and HasOracle finite-value witnesses; reason: indexing permits repeated data and the empty family without changing the existence claim; witnesses range over the full extended-valued source class
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, Lemma 2, p. 9 (PDF 9), https://arxiv.org/abs/1502.05666v6

import Mathlib
import Definitions.Def_TaylorHGAudit_PEP_Class

namespace TaylorHGAudit.PEP

theorem conjugate_data {d : ℕ} {ι : Type*} [Fintype ι]
    (L : ENNReal) (hL : 0 < L) (x g : ι → E d) (v : ι → ℝ) :
    Interpolable 0 L x g v ↔
      Interpolable (L⁻¹).toNNReal ⊤ g x
        (fun i => inner ℝ (x i) (g i) - v i) := by sorry

end TaylorHGAudit.PEP
