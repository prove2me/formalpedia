-- Prove2me | Theorems.Thm_TightCoreset2027_Euclidean_projection_family_of_binary_code
-- name    : TightCoreset2027.Euclidean.projection_family_of_binary_code
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:59:16.06025+00:00
-- url     : https://prove2.me/theorems/68f14ab0-7dfa-4b39-8d03-be203ff6027f
-- title:
--   Realizing a binary code as a joint-discrepancy projection family
-- statement:
--   Let $L,q\ge1$, and let $S\subseteq\mathbb F_2^L$ consist of $q$ distinct binary words with no four distinct words summing to zero. There are distinct unit vectors $x_1,\ldots,x_q\in\mathbb R^{2L}$ and a nonempty finite set $V$ of vectors of squared norm two. For each $s$ and $v\in V$, an integer $\ell(s;v)\in\{0,\ldots,L\}$ satisfies
--
--   $$\langle x_s,v\rangle=1-\frac{2\ell(s;v)}L.$$
--
--   For every $t\ge1$ and every $A^{(1)},\ldots,A^{(t)}\in\mathbb R^q$, one common direction satisfies
--
--   $$\sum_{r=1}^t\left|\sum_{s=1}^q A_s^{(r)}(-1)^{\ell(s;v)}\right|\ge\frac1{\sqrt3}\sum_{r=1}^t\|A^{(r)}\|_2.$$
--
--   This is the geometric and moment component of Lemma 2.1 after its initial code selection. The family depends only on the supplied code, before the coefficients are chosen.
-- source:
--   Hu–Huang–Li–Xu, Tight Coreset Bounds for (k,z)-Clustering in Euclidean and Doubling Metrics, STOC 2027 submission #879, §2.4, proof of Lemma 2.1 after the greedy construction, Eqs. (15)–(16), printed pp. 16–18 / PDF pp. 18–20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/879.pdf

import Definitions.Def_TightCoreset2027_Euclidean_projectionModel
open scoped BigOperators
set_option autoImplicit false

namespace TightCoreset2027.Euclidean
 theorem projection_family_of_binary_code (L q : ℕ) (hL : 1 ≤ L) (hq : 1 ≤ q)
    (S : Finset (Fin L → ZMod 2)) (hS : S.card = q)
    (hfour : ∀ T ⊆ S, T.card = 4 → ∑ x ∈ T, x ≠ 0) :
    ∃ G : ProjectionFamily L q, ProjectionSpecification G := by sorry
end TightCoreset2027.Euclidean
