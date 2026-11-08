-- Prove2me | Theorems.Thm_ReusableMatching_theorem_1_min_f
-- name    : ReusableMatching.theorem_1_min_f
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T05:33:19.696843+00:00
-- url     : https://prove2.me/theorems/2df3a785-05b3-4614-afe9-5a68598519ba
-- title:
--   Proof of Theorem 1: $f(z_1,z_2,x)>0.5893$ at $\beta=0.89$
-- statement:
--   Let $\beta=0.89$, $g(x)=e^{\beta(x-1)}$, $G(x)=g(x)/\beta$ and
--
--   $$
--   f(z_1,z_2,x)=G(z_2)-G(z_1)+(1-g(x))(1-z_1)+(1-z_2)\bigl(G(x)-G(0)\bigr)+z_1\bigl(1-g(0)\bigr).
--   $$
--
--   Then for all $0\le z_1\le z_2\le 1$ and $x\in[0,1]$,
--
--   $$
--   f(z_1,z_2,x)\ >\ 0.5893 .
--   $$
--
--   Combined with Lemma 9, this gives the conditional bound (3) with $\Gamma=0.5893$ for every edge, which is the numerical heart of Theorem 1. The minimum is close to the bound: it is about $0.58931$.
--
--   Differences from the source:
--   - reading: "min f(z1,z2,x) > 0.589 for β = 0.89" and "both terms are greater than 0.5893" → f(z1,z2,x) > 0.5893 at every point of the domain; reason: the end of the proof establishes 0.5893, the stronger of the two constants; the minimum over the compact domain is attained, so a strict bound at every point is the bound on the minimum
--   - encoding: G is an antiderivative of g → G(x) = g(x)/β; reason: only differences of G occur
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, proof of Theorem 1, p.13 ("both terms are greater than 0.5893")

import Mathlib
import Definitions.Def_ReusableMatching_fBound

namespace ReusableMatching

/-- **The minimization in the proof of Theorem 1** of Delong, Farhadi, Niazadeh, Sivan & Udwani,
arXiv:2110.07084v2, p.13: with
`f(z1, z2, x) = G(z2) − G(z1) + (1 − g(x))(1 − z1) + (1 − z2)(G(x) − G(0)) + z1(1 − g(0))`,
"We show that, `min_{0 ≤ z1 ≤ z2 ≤ 1, x ∈ [0,1]} f(z1, z2, x) > 0.589` for `β = 0.89`", and, at the
end of the proof, "It is easy to (numerically) verify that when `β = 0.89`, both terms are greater
than `0.5893`, giving us the desired guarantee."

The statement: for `β = 0.89`, `f(z1, z2, x) > 0.5893` for all `0 ≤ z1 ≤ z2 ≤ 1` and
`x ∈ [0, 1]`.

**Formalization Note.** The minimum over the compact domain is attained, so "the minimum exceeds
`0.5893`" is the strict inequality at every point. The constant is the `0.5893` of the end of the
proof (and of "Γ ≈ 0.5893", p.8), which is stronger than the `0.589` of the first sentence.
`G(x) = g(x)/β`. -/
theorem theorem_1_min_f (z1 z2 x : ℝ) (hz1 : 0 ≤ z1) (hz12 : z1 ≤ z2) (hz2 : z2 ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (5893 / 10000 : ℝ) < fBound (89 / 100) z1 z2 x := by sorry

end ReusableMatching
