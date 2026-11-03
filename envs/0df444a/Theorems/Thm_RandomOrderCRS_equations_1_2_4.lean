-- Prove2me | Theorems.Thm_RandomOrderCRS_equations_1_2_4
-- name    : RandomOrderCRS.equations_1_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:23:54.374135+00:00
-- url     : https://prove2.me/theorems/a4663d00-0433-42a9-a1d4-aa26fec82a2f
-- title:
--   §3.1, equations (1), (2), (4) — the bound by $\int_0^1\mathrm{obj}_G(e,y)\,dy$
-- statement:
--   Let $G$ be 1-regular with respect to $x$ and $a=a_1$, and let $e$ be an edge. Then:
--
--   1. equation (1): $\mathbb P[e\in\mathcal M\mid S_e=1]\ge\mathbb P[|\mathcal R_e|=0]+\sum_{f\in\partial(e)}\mathbb P[\mathrm{sbl}_f\text{ and }\mathcal R_e=\{f\}]$;
--   2. equation (2): for $y\in[0,1]$, $\mathbb P[|\mathcal R_e|=0\mid Y_e=y]=\prod_{f\in\partial(e)}\ell(x_f,y)$;
--   3. after equation (4): $\mathbb P[e\in\mathcal M\mid S_e=1]\ge\int_0^1\mathrm{obj}_G(e,y)\,dy$.
--
--   Item 3 is what the remaining argument minimizes.
--
--   Differences from the source:
--   - encoding: $\mathbb P[e\in\mathcal M\mid S_e=1]\ge B$ in items 1 and 3 → $s(x_e)\cdot B\le\mathbb P[e\in\mathcal M]$; reason: $e\in\mathcal M$ implies $S_e=1$, $\mathbb P[S_e=1]=s(x_e)$, and this covers $x_e=0$
--   - encoding: conditioning on the null event $Y_e=y$ → `atTime`: $Y_e$ is set to the parameter $y$ and the other coordinates are integrated; reason: the $Y_g$ are independent, so this is the regular conditional probability
--   - encoding: $\mathrm{obj}_G$ with the printed $T$ → `obj` with $T$ through $\tau$; reason: it equals the printed formula for $xy\ne0$ and its limits at $xy=0$
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, §3.1, equations (1), (2), (4), pp.19–20

import Mathlib
import Definitions.Def_RandomOrderCRS_FractionalMatching
import Definitions.Def_RandomOrderCRS_Attenuation
import Definitions.Def_RandomOrderCRS_ArrivalModel
import Definitions.Def_RandomOrderCRS_SimpleBlocker
import Definitions.Def_RandomOrderCRS_Objective

namespace RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

/-- MacRury, Ma & Grammel, arXiv:2209.07520v2, §3.1, equations (1), (2) and (4), pp.19–20, for
`a = a₁` and `G` 1-regular:
1. equation (1): `ℙ[e ∈ ℳ | S_e = 1] ≥ ℙ[|ℛ_e| = 0] + ∑_{f∈∂(e)} ℙ[sbl_f and ℛ_e = {f}]`;
2. equation (2): `ℙ[|ℛ_e| = 0 | Y_e = y] = ∏_{f∈∂(e)} ℓ(x_f, y)`;
3. after (4): `ℙ[e ∈ ℳ | S_e = 1] ≥ ∫₀¹ obj_G(e, y) dy`.

**Formalization Note.** Items 1 and 3 are multiplied by `ℙ[S_e = 1] = s(x_e)`, which covers
`x_e = 0`. In this form they are the bounds on `ℙ[e ∈ ℳ]`, since `e ∈ ℳ` implies `S_e = 1`. -/
theorem equations_1_2_4 (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (hx : IsOneRegular G x) (e : G.edgeSet) :
    survival a₁ (x e) *
        (arrivalProb G x a₁ (fun Y S => relevantSet G Y S e = ∅) +
          ∑ f ∈ edgeNbrs G e, arrivalProb G x a₁
            (fun Y S => HasSimpleBlocker G Y S e f ∧ relevantSet G Y S e = {f})) ≤
      arrivalProb G x a₁ (fun Y S => e ∈ greedy G (arrivalOrder G Y) S) ∧
    (∀ y ∈ Set.Icc (0 : ℝ) 1,
      arrivalProb G x a₁ (atTime G e y fun Y S => relevantSet G Y S e = ∅) =
        ∏ f ∈ edgeNbrs G e, ell a₁ (x f) y) ∧
    survival a₁ (x e) * ∫ y in (0 : ℝ)..1, obj a₁ G x e y ≤
      arrivalProb G x a₁ (fun Y S => e ∈ greedy G (arrivalOrder G Y) S) := by sorry

end RandomOrderCRS
