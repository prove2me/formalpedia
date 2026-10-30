-- Prove2me | Theorems.Thm_TaylorHGAudit_PEP_conjugate_curvature
-- name    : TaylorHGAudit.PEP.conjugate_curvature
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:51:34.076993+00:00
-- url     : https://prove2.me/theorems/44935693-0a23-47f6-88f5-ab8195bc51aa
-- title:
--   Theorem 2 — smoothness and conjugate curvature for extended-valued functions
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R\cup\{+\infty\}$ be proper, closed and convex, and let $0<L\le+\infty$. Its actual conjugate is $F^*(y)=\sup_x\{\langle x,y\rangle-F(x)\}$. Then
--
--   $$F\in\mathcal F_{0,L}\quad\Longleftrightarrow\quad F^*\in\mathcal F_{1/L,+\infty}.$$
--
--   Here $1/+\infty=0$. The conjugate is computed from $F$ and may take $+\infty$ even when $F$ is real-valued everywhere. This is the class equivalence underlying the conjugation of interpolation data.
--
--   Differences from the source:
--   - encoding: finite nonnegative curvature and extended positive smoothness on Euclidean space → NNReal curvature, ENNReal smoothness, EReal function values and real-height epigraph convexity; reason: the strict parameter hypothesis excludes zero smoothness and preserves every source instance, including infinite smoothness; only finite quadratic values are subtracted
--   - encoding: proper closed convex functions and the Legendre–Fenchel conjugate → published GammaZero and the computed EReal-valued MoreauProx.Decomposition.conj; reason: lower semicontinuity is closed epigraph here and conjugation takes the true extended supremum, including infinite values
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, Theorem 2, p. 8 (PDF 8), https://arxiv.org/abs/1502.05666v6

import Mathlib
import Definitions.Def_TaylorHGAudit_PEP_Class

namespace TaylorHGAudit.PEP

theorem conjugate_curvature {d : ℕ} (L : ENNReal) (hL : 0 < L)
    (F : E d → EReal) (hF : MoreauProx.Decomposition.GammaZero F) :
    FClass 0 L F ↔
      FClass (L⁻¹).toNNReal ⊤ (MoreauProx.Decomposition.conj F) := by sorry

end TaylorHGAudit.PEP
