-- Prove2me | Theorems.Thm_StreamSubmod_Supplement_lemma_23
-- name    : StreamSubmod.Supplement.lemma_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:45:41.961586+00:00
-- url     : https://prove2.me/theorems/35894a1e-af04-4e43-9417-22d6adceeea4
-- title:
--   Lemma 23: $F(x+y)\ge(1-p)F(x)$ for $y\le p$ with support disjoint from $x$
-- statement:
--   Let $f:2^V\to\mathbb R_{\ge0}$ be a non-negative submodular function on a finite ground set $V$, with multilinear extension $F$, let $p\in[0,1]$, and let $x,y\in[0,1]^V$ be such that
--
--   1. $\operatorname{supp}(x)\cap\operatorname{supp}(y)=\varnothing$, and
--   2. $y_e\le p$ for every $e\in V$.
--
--   Then
--
--   $$
--   F(x+y)\ \ge\ (1-p)\cdot F(x).
--   $$
--
--   The lemma bounds how much the value of $F$ can drop when a vector with small coordinates on new elements is added; it is used for both lower bounds of the case $\|\hat x\|_1<k$.
--
--   Differences from the source:
--   - encoding: f : 2^V → ℝ≥0 → f : Finset E → ℝ with ∀ S, 0 ≤ f S; reason: the same functions
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Lemma 23, pp.23–24

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_StreamSubmod_Supplement_Basic

namespace StreamSubmod.Supplement

open NonmonotoneSubmod.Shared in
/-- Lemma 23 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, pp.23–24): let
`f : 2^V → ℝ≥0` be a non-negative submodular function, let `p` be a number in the range `[0, 1]` and
let `x, y` be two vectors in `[0, 1]^V` such that `supp(x) ∩ supp(y) = ∅` and `y_e ≤ p` for every
`e ∈ V`. Then, the multilinear extension `F` of `f` obeys `F(x + y) ≥ (1 − p) · F(x)`. -/
theorem lemma_23 {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x y : E → ℝ) (hx0 : ∀ e, 0 ≤ x e) (hx1 : ∀ e, x e ≤ 1) (hy0 : ∀ e, 0 ≤ y e)
    (hy1 : ∀ e, y e ≤ 1) (hxy : Disjoint (supp x) (supp y)) (hyp : ∀ e, y e ≤ p) :
    (1 - p) * F f x ≤ F f (fun e => x e + y e) := by sorry

end StreamSubmod.Supplement
