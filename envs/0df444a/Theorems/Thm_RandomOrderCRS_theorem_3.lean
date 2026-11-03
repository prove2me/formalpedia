-- Prove2me | Theorems.Thm_RandomOrderCRS_theorem_3
-- name    : RandomOrderCRS.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:59.559196+00:00
-- url     : https://prove2.me/theorems/4548d63c-c475-43d0-8ea7-306e39fc7d80
-- title:
--   Theorem 3 — Algorithm 2 is $c^*$-selectable on 1-regular graphs
-- statement:
--   Let $G$ be a finite graph that is 1-regular with respect to $x$. Algorithm 2 with the attenuation function $a_1(x)=(1-(3-e)x)^2$ selects each edge $e$ with probability at least $c^*x_e$ when the edges arrive in uniformly random order, where
--
--   $$c^*=\frac{e^2-4e^3+e^4+20e-22}{4e^2}\ge0.474035.$$
--
--   Differences from the source:
--   - encoding: Algorithm 2 with a uniformly random order → `attenuateROM` as a `Policy`, with `IsRCRSelectable`; reason: the average over all $|E|!$ orders is the uniform order; the bound is unconditional, as on p.3
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Theorem 3, p.17; proof in §3.1, pp.21–22

import Mathlib
import Definitions.Def_RandomOrderCRS_FractionalMatching
import Definitions.Def_RandomOrderCRS_Policy
import Definitions.Def_RandomOrderCRS_Attenuation
import Definitions.Def_RandomOrderCRS_AttenuateROM

namespace RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Theorem 3, MacRury, Ma & Grammel, arXiv:2209.07520v2, p.17: "If a(x) = a₁(x), where
a₁(x) := (1 − (3 − e)x)², then Algorithm 2 is (e²−4e³+e⁴+20e−22)/(4e²) ≥ 0.474035 selectable for
1-regular general graphs." -/
theorem theorem_3 (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (hx : IsOneRegular G x) :
    IsRCRSelectable G (attenuateROM G x a₁ hx.isFractionalMatching a₁_mem_Icc) x cStar ∧
    (0.474035 : ℝ) ≤ cStar := by sorry

end RandomOrderCRS
