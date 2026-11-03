-- Prove2me | Theorems.Thm_RandomOrderCRS_lemma_4
-- name    : RandomOrderCRS.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:23:42.343674+00:00
-- url     : https://prove2.me/theorems/03f8aca3-48b0-438e-b5ae-2e7db709f215
-- title:
--   Lemma 4 — vertex splitting
-- statement:
--   Let $a=a_1$. Fix a vertex $w\in N(u)\cup N(v)\setminus\{u,v\}$ of a neighbourhood of $e=(u,v)$. For $k\ge1$, let $G_k$ replace $w$ by $k$ copies, splitting the values of the edges at $w$ uniformly. Then
--
--   $$\int_0^1\mathrm{obj}_G(e,y)\,dy\ge\lim_{k\to\infty}\int_0^1\mathrm{obj}_{G_k}(e,y)\,dy.$$
--
--   In terms of pairs: for a finite family of pairs $(p_i,q_i)$ and a pair $(p_0,q_0)$, all non-negative with $p+q\le1$, replacing $(p_0,q_0)$ by $k$ copies of $(p_0/k,q_0/k)$ gives integrals that converge as $k\to\infty$, to a limit no larger than the value for the original family. Iterating over all neighbours leads to the Poisson regime of equation (6).
--
--   Differences from the source:
--   - generalization: a statement about $\mathrm{obj}_G$ and the graph $G_k$ → a statement about `objPairs` for any finite family of pairs with $p,q\ge0$ and $p+q\le1$; reason: $\mathrm{obj}_G$ is `objPairs` of the neighbour family (proved in a verification file), and on ec17–ec19 $G_k$ is used only through this formula, since it need not be 1-regular
--   - encoding: $\lim_{k\to\infty}$ → existence of $L$ with `Tendsto` and the bound on $L$; reason: the limit is asserted to exist, so no junk value of `limUnder` can enter
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Lemma 4, p.21; §C.6, ec17–ec19

import Mathlib
import Definitions.Def_RandomOrderCRS_Attenuation
import Definitions.Def_RandomOrderCRS_SimpleBlocker
import Definitions.Def_RandomOrderCRS_Objective

open Filter Topology

namespace RandomOrderCRS

/-- Lemma 4 (Vertex Splitting), MacRury, Ma & Grammel, arXiv:2209.07520v2, p.21, for `a = a₁`:
`∫₀¹ obj_G(e, y) dy ≥ lim_{k→∞} ∫₀¹ obj_{G_k}(e, y) dy`, where `G_k` replaces one vertex `w` of
`N(u) ∪ N(v) \ {u, v}` by `k` copies with `x′_{wᵢ,r} := x_{w,r}/k`.

**Formalization Note.** Stated for the function `objPairs` of the pairs `(p_w, q_w)`, which is
`obj_G` (grouping `f` and `fᶜ`), and the family with `(p₀, q₀)` replaced by `k` copies of
`(p₀/k, q₀/k)`. This covers every graph, since `p_w, q_w ≥ 0` and `p_w + q_w ≤ 1` by the degree
constraint at `w`. `G_k` itself need not be 1-regular and is used only through this formula. The
limit is asserted to exist. The term `k = 1` is the family of `G`. -/
theorem lemma_4 {ι : Type} [Fintype ι] [DecidableEq ι] (p q : ι → ℝ) (p₀ q₀ : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hpq : ∀ i, p i + q i ≤ 1)
    (hp₀ : 0 ≤ p₀) (hq₀ : 0 ≤ q₀) (hpq₀ : p₀ + q₀ ≤ 1) :
    ∃ L : ℝ,
      Tendsto (fun k : ℕ => ∫ y in (0 : ℝ)..1,
        objPairs a₁ (splitFamily p p₀ k) (splitFamily q q₀ k) y) atTop (𝓝 L) ∧
      L ≤ ∫ y in (0 : ℝ)..1, objPairs a₁ (splitFamily p p₀ 1) (splitFamily q q₀ 1) y := by sorry

end RandomOrderCRS
