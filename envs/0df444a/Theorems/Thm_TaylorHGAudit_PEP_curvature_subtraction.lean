-- Prove2me | Theorems.Thm_TaylorHGAudit_PEP_curvature_subtraction
-- name    : TaylorHGAudit.PEP.curvature_subtraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:49:07.958916+00:00
-- url     : https://prove2.me/theorems/3ae3d5fd-f2e6-461e-ab30-40bcf518befc
-- title:
--   Theorem 3 — minimal curvature subtraction for the full source class
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R\cup\{+\infty\}$ be proper, closed and convex, and let $0\le\mu<L\le+\infty$ with finite $\mu$. Then
--
--   $$F\in\mathcal F_{\mu,L}\quad\Longleftrightarrow\quad
--   \left[x\mapsto F(x)-\frac\mu2\|x\|^2\right]\in\mathcal F_{0,L-\mu}.$$
--
--   The convention is $+\infty-\mu=+\infty$. This equivalence transfers the source's full function class under removal of its minimal curvature. Unlike the related already Open real-valued statement, $F$ may have a proper effective domain.
--
--   Differences from the source:
--   - encoding: finite nonnegative curvature and extended positive smoothness on Euclidean space → NNReal curvature, ENNReal smoothness, EReal function values and real-height epigraph convexity; reason: the strict parameter hypothesis excludes zero smoothness and preserves every source instance, including infinite smoothness; only finite quadratic values are subtracted
--   - encoding: proper closed convex functions → published GammaZero; reason: lower semicontinuity is equivalent to a closed epigraph here
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, Theorem 3, p. 8 (PDF 8), https://arxiv.org/abs/1502.05666v6

import Mathlib
import Definitions.Def_TaylorHGAudit_PEP_Class

namespace TaylorHGAudit.PEP

theorem curvature_subtraction {d : ℕ} (μ : NNReal) (L : ENNReal)
    (hμL : (μ : ENNReal) < L) (F : E d → EReal)
    (hF : MoreauProx.Decomposition.GammaZero F) :
    FClass μ L F ↔ FClass 0 (L - (μ : ENNReal)) (subtractCurvature μ F) := by sorry

end TaylorHGAudit.PEP
