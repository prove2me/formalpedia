-- Prove2me | Theorems.Thm_TaylorHGAudit_PEP_interpolation
-- name    : TaylorHGAudit.PEP.interpolation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:52:40.311961+00:00
-- url     : https://prove2.me/theorems/da0967e0-e08b-4865-b2be-9cd022dc965c
-- title:
--   Theorem 4 — exact interpolation iff over the full source class
-- statement:
--   Let $0\le\mu<L\le+\infty$, and let $(x_i,g_i,v_i)_{i\in I}$ be finite Euclidean data with real values. Put $q=1/L$, using $q=0$ at infinity. The family is interpolable by one proper closed function in $\mathcal F_{\mu,L}$ if and only if every ordered pair $i,j\in I$ satisfies
--
--   $$v_i-v_j-\langle g_j,x_i-x_j\rangle\ge
--   \frac{q\|g_i-g_j\|^2+\mu\|x_i-x_j\|^2-2\mu q\langle g_j-g_i,x_j-x_i\rangle}{2(1-\mu q)}.$$
--
--   This is the full-source interpolation equivalence used by Theorem 5. The referenced Proved real-valued Theorem 4 supplies sufficient witnesses after proper closed embedding; the new necessity direction covers all extended-valued source functions, rather than assuming full-domain finiteness.
--
--   Differences from the source:
--   - encoding: finite nonnegative curvature and extended positive smoothness on Euclidean space → NNReal curvature, ENNReal smoothness, EReal function values and real-height epigraph convexity; reason: the strict parameter hypothesis excludes zero smoothness and preserves every source instance, including infinite smoothness; only finite quadratic values are subtracted
--   - encoding: a finite set of triples with real values and Euclidean points and subgradients → an arbitrary Fintype index, EuclideanSpace vectors and HasOracle finite-value witnesses; reason: indexing permits repeated data and the empty family without changing the existence claim; witnesses range over the full extended-valued source class
--   - encoding: the ordered-pair inequality (4) with the convention 1/+∞ = 0 → published TaylorHG.PEP.InterpIneq with reciprocal smoothness; reason: the imported predicate has exactly the same inner products, constants and all ordered pairs; its use does not import the old real-valued function class
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, Theorem 4, p. 10 (PDF 10), https://arxiv.org/abs/1502.05666v6

import Mathlib
import Definitions.Def_TaylorHGAudit_PEP_Class

namespace TaylorHGAudit.PEP

theorem interpolation {d : ℕ} {ι : Type*} [Fintype ι]
    (μ : NNReal) (L : ENNReal) (hμL : (μ : ENNReal) < L)
    (x g : ι → E d) (v : ι → ℝ) :
    Interpolable μ L x g v ↔ ∀ i j, TaylorHG.PEP.InterpIneq μ L x g v i j := by sorry

end TaylorHGAudit.PEP
