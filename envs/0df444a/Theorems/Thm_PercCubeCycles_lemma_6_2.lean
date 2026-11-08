-- Prove2me | Theorems.Thm_PercCubeCycles_lemma_6_2
-- name    : PercCubeCycles.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:36.131202+00:00
-- url     : https://prove2.me/theorems/78fba708-665a-4f47-ad44-29f27633963c
-- title:
--   Lemma 6.2 — the number of special $(a,b)$-trees rooted at $v$ with $k$ vertices
-- statement:
--   Let $H$ be a graph of maximum degree at most $d$, let $v\in V(H)$, and let $k\ge3$, $a,b\ge0$ be integers. Let $t(v,a,b,k)$ be the number of $H$-special $(a,b)$-trees rooted at $v$, with $k$ vertices, in which $v$ has degree at least 3. If $k\ge4(a+b)$, then
--   $$t(v,a,b,k)\le(a+b)\,d^{k-1}\left(\frac{2e^3k}{a+2b}\right)^{a+2b}.$$
--   This is the sharper count that gives the expansion bounds of §6.
--
--   Differences from the source:
--   - encoding: a graph → a graph on a finite type; reason: the paper considers finite graphs
--   - encoding: the bound at $a+2b=0$ → the right side is $0$ (factor $a+b=0$, and $0$-th power $1$); reason: no such tree exists, since a tree on at least three vertices has at least two leaves
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Lemma 6.2, p.19

import Mathlib
import Definitions.Def_PercCubeCycles_Trees

set_option autoImplicit false

namespace PercCubeCycles

/-- Lemma 6.2, p.19, Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). Let `H` be a graph of maximum degree at most `d`, `v ∈ V(H)`, `k ≥ 3` and
`a, b ≥ 0`. The number `t(v, a, b, k)` of `H`-special `(a, b)`-trees rooted at `v`, with `k` vertices,
in which `v` has degree at least 3, satisfies, if `k ≥ 4(a + b)`,
`t(v, a, b, k) ≤ (a + b) d^{k−1} (2e³k/(a + 2b))^{a+2b}`.

**Formalization Note.** Trees are subtrees of `H`. For `a + 2b = 0` the right side is `0`, which is
correct: a tree on at least three vertices has at least two leaves, so no such tree exists. -/
theorem lemma_6_2 {V : Type*} [Fintype V] (H : SimpleGraph V) (d : ℕ) (hH : ∀ u, deg H u ≤ d)
    (v : V) (k a b : ℕ) (hk : 3 ≤ k) (hab : 4 * (a + b) ≤ k) :
    ({T : H.Subgraph | IsSpecial H T a b ∧ v ∈ T.verts ∧ T.verts.ncard = k ∧ 3 ≤ treeDeg T v}.ncard : ℝ)
      ≤ ((a : ℝ) + b) * (d : ℝ) ^ (k - 1) *
          (2 * Real.exp 3 * k / ((a : ℝ) + 2 * b)) ^ (a + 2 * b) := by sorry

end PercCubeCycles
