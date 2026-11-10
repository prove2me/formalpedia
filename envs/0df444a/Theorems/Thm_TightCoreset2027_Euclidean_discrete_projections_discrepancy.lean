-- Prove2me | Theorems.Thm_TightCoreset2027_Euclidean_discrete_projections_discrepancy
-- name    : TightCoreset2027.Euclidean.discrete_projections_discrepancy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:06:43.325144+00:00
-- url     : https://prove2.me/theorems/97f173e3-cdef-425e-b242-2a5759d6ece5
-- title:
--   Lemma 2.1 — discrete projections and a discrepancy bound
-- statement:
--   Let $L,q\ge1$ be integers such that $2^L>q+\binom q3$. There exist distinct unit vectors $x_1,\ldots,x_q\in\mathbb R^{2L}$ and a nonempty finite set $V\subseteq\mathbb R^{2L}$ with $\|v\|^2=2$ for every $v\in V$. Every projection has a level $\ell(s;v)\in\{0,\ldots,L\}$ satisfying $\langle x_s,v\rangle=1-2\ell(s;v)/L$. For every integer $t\ge1$ and every fixed coefficient family $A^{(r)}\in\mathbb R^q$,
--
--   $$\max_{v\in V}\sum_{r=1}^t\left|\sum_{s=1}^q A_s^{(r)}(-1)^{\ell(s;v)}\right|\ge\frac1{\sqrt3}\sum_{r=1}^t\|A^{(r)}\|_2.$$
--
--   The vectors and directions are chosen before the coefficient family. This supplies both the finite projection grid and the common direction required by the error estimate.
--
--   Differences from the source:
--   - encoding: distinct vectors, a finite direction set, and the induced level index → a raw ProjectionFamily satisfying all clauses of ProjectionSpecification; reason: the index is stored with its defining equality; positivity of L makes the grid injective
--   - encoding: a lower bound on the maximum over V → there exists a direction in V attaining at least the displayed bound; reason: V is finite and nonempty, so the two statements are equivalent
--   - encoding: indices starting at 1 and levels from 0 through L → Fin q, Fin t and Fin (L+1); reason: bijections preserve every vector, coefficient family, norm and sum
-- source:
--   Junqiu Hu, Lingxiao Huang, Jian Li, Baoduo Xu, STOC 2027 submission #879 (October 2026), Lemma 2.1, Eq. (3)–(4), printed p. 10 / PDF p. 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/879.pdf

import Definitions.Def_TightCoreset2027_Euclidean_projectionModel
set_option autoImplicit false

namespace TightCoreset2027.Euclidean

theorem discrete_projections_discrepancy (L q : ℕ) (hL : 1 ≤ L) (hq : 1 ≤ q)
    (hcode : q + Nat.choose q 3 < 2 ^ L) :
    ∃ G : ProjectionFamily L q, ProjectionSpecification G := by sorry

end TightCoreset2027.Euclidean
