-- Prove2me | Theorems.Thm_RandomOrderCRS_lemma_3
-- name    : RandomOrderCRS.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:45.11035+00:00
-- url     : https://prove2.me/theorems/8764a85c-52e5-44c0-b984-9115201f56f0
-- title:
--   Lemma 3 — lower bound for some simple-blocker
-- statement:
--   Let $G$ be 1-regular with respect to $x$ and $a=a_1$. For each $f\in\partial(e)$ and $y\in[0,1]$,
--
--   $$\mathbb P[\mathrm{sbl}_f\mid\mathcal R_e=\{f\},Y_e=y]\ge T(x_f+x_{f^c},y).$$
--
--   The worst case is that $w$ has a single other neighbour, with edge value $1-x_f-x_{f^c}$. This is the opposite worst case to that of Lemma 2.
--
--   Differences from the source:
--   - encoding: the conditional probability given $\mathcal R_e=\{f\}$ → the joint form $\text{bound}\cdot\mathbb P[\mathcal R_e=\{f\}]\le\mathbb P[\text{event},\mathcal R_e=\{f\}]$; reason: it agrees with the conditional when the event has positive probability, and it is meaningful at $x_f=0$ and $y=0$
--   - encoding: conditioning on the null event $Y_e=y$ → `atTime`: $Y_e$ is set to the parameter $y$ and the other coordinates are integrated; reason: the $Y_g$ are independent, so this is the regular conditional probability
--   - encoding: $T$ with the printed formula → $T$ through $\tau$; reason: it equals the printed formula for $xy\ne0$ and its limits at $xy=0$
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Lemma 3, p.20; §C.4, ec16–ec17

import Mathlib
import Definitions.Def_RandomOrderCRS_FractionalMatching
import Definitions.Def_RandomOrderCRS_Attenuation
import Definitions.Def_RandomOrderCRS_ArrivalModel
import Definitions.Def_RandomOrderCRS_SimpleBlocker

namespace RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Lemma 3 (Second-order minimization), MacRury, Ma & Grammel, arXiv:2209.07520v2, p.20, for
`a = a₁` and `G` 1-regular: for each `f ∈ ∂(e)`,
`ℙ[sbl_f | ℛ_e = {f}, Y_e = y] ≥ T(x_f + x_{fᶜ}, y)`.

**Formalization Note.** In joint form, as for `lemma_2`. `T` is the function of p.20, with the
values at `xy = 0` given by its limits. -/
theorem lemma_3 (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (hx : IsOneRegular G x) (e f : G.edgeSet) (hf : f ∈ edgeNbrs G e)
    (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    T a₁ (x f + x (pair (e : Sym2 V) (f : Sym2 V))) y *
      arrivalProb G x a₁ (atTime G e y fun Y S => relevantSet G Y S e = {f}) ≤
    arrivalProb G x a₁
      (atTime G e y fun Y S => HasSimpleBlocker G Y S e f ∧ relevantSet G Y S e = {f}) := by sorry

end RandomOrderCRS
