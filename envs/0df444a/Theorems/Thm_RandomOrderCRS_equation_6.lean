-- Prove2me | Theorems.Thm_RandomOrderCRS_equation_6
-- name    : RandomOrderCRS.equation_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:24:16.132831+00:00
-- url     : https://prove2.me/theorems/04f25fe6-24c3-430f-98e8-b8bd535c218f
-- title:
--   §3.1, equation (6) — the Poisson-regime lower bound
-- statement:
--   Let $G$ be 1-regular with respect to $x$ and $a=a_1$. For each edge $e$,
--
--   $$\int_0^1\mathrm{obj}_G(e,y)\,dy\ge\int_0^1e^{-2(1-x_e)y}\big(1+a(1)(1-x_e)y^2\big)\,dy.$$
--
--   Here $a(1)=a_1(1)=(e-2)^2$. The right side depends only on $x_e$, so this removes the graph from the problem.
--
--   Differences from the source:
--   - encoding: $\mathrm{obj}_G$ with the printed $T$ → `obj` with $T$ through $\tau$; reason: it equals the printed formula for $xy\ne0$ and its limits at $xy=0$
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, §3.1, equation (6), p.22

import Mathlib
import Definitions.Def_RandomOrderCRS_FractionalMatching
import Definitions.Def_RandomOrderCRS_Attenuation
import Definitions.Def_RandomOrderCRS_SimpleBlocker
import Definitions.Def_RandomOrderCRS_Objective

open Real

namespace RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

/-- MacRury, Ma & Grammel, arXiv:2209.07520v2, §3.1, equation (6), p.22, for `a = a₁` and `G`
1-regular: `∫₀¹ obj_G(e, y) dy ≥ ∫₀¹ e^{−2(1−x_e)y}(1 + a(1)(1 − x_e)y²) dy`.

**Formalization Note.** `a(1)` is the constant `a₁ 1 = (e − 2)²`. The step
`∑_{f∈∂(e)} x_f = 2(1 − x_e)` uses 1-regularity at both endpoints of `e`. -/
theorem equation_6 (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (hx : IsOneRegular G x) (e : G.edgeSet) :
    ∫ y in (0 : ℝ)..1, exp (-2 * (1 - x e) * y) * (1 + a₁ 1 * (1 - x e) * y ^ 2) ≤
      ∫ y in (0 : ℝ)..1, obj a₁ G x e y := by sorry

end RandomOrderCRS
