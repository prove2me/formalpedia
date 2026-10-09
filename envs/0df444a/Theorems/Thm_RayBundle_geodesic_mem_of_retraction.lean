-- Prove2me | Theorems.Thm_RayBundle_geodesic_mem_of_retraction
-- name    : RayBundle.geodesic_mem_of_retraction
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-10-08T18:56:46.340995+00:00
-- url     : https://prove2.me/theorems/acf1402e-d9cb-462c-8c08-ca1168938517
-- title:
--   Edge contraction and exit collapse force geodesic convexity
-- statement:
--   Let $X$ be a connected simple graph, $L\subseteq V(X)$, and $r:V(X)\to V(X)$ a map fixing every vertex of $L$. Suppose $d_X(r(a),r(b))\le1$ whenever $a,b$ are adjacent, and $r(b)=a$ whenever $a\in L$, $b\notin L$, and $a,b$ are adjacent. Then every shortest walk with both endpoints in $L$ has all its vertices in $L$. The statement needs only these local conditions on $r$; it does not require a global range condition $r(V)\subseteq L$.
-- source:
--   General graph convexity criterion proved in the supplied Lean development. Its application to ladder convexity is motivated by Proposition 4.2 of Nicholas Touikan, On geodesic ray bundles in hyperbolic groups (2018). https://arxiv.org/abs/1706.01979

import Mathlib.Combinatorics.SimpleGraph.Metric

theorem RayBundle.geodesic_mem_of_retraction {V : Type*} {X : SimpleGraph V}
    (hX : X.Connected) (L : Set V) (r : V → V)
    (hfix : ∀ v ∈ L, r v = v)
    (hstep : ∀ {a b}, X.Adj a b → X.dist (r a) (r b) ≤ 1)
    (hexit : ∀ {a b}, a ∈ L → b ∉ L → X.Adj a b → r b = a)
    {a b : V} (w : X.Walk a b) (hw : w.length = X.dist a b)
    (ha : a ∈ L) (hb : b ∈ L) : ∀ v ∈ w.support, v ∈ L := by sorry
