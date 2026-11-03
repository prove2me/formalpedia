-- Prove2me | Theorems.Thm_RandomOrderCRS_lemma_2
-- name    : RandomOrderCRS.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:46.030363+00:00
-- url     : https://prove2.me/theorems/40178d03-39dd-4f84-9f01-b6f9cf8e4865
-- title:
--   Lemma 2 — lower bound for a fixed simple-blocker
-- statement:
--   Let $G$ be 1-regular with respect to $x$ and $a=a_1$. Let $f\in\partial(e)$ have vertex $w$ not in $e$, let $h\in\partial(w)\setminus\{f,f^c\}$, and let $y\in[0,1]$. With $z:=2(1-x_h)-x_f-x_{f^c}$,
--
--   $$\mathbb P[\mathrm{sbl}_f(h)\mid\mathcal R_e=\{f\},Y_e=y]\ge\frac{s(x_h)}{z}\left(1-\frac{1-e^{-zy}}{zy}\right).$$
--
--   The bound corresponds to all the edges $h'\in\partial(h)\setminus\partial(e)$ having infinitesimally small values. It is the first level of the second-order analysis.
--
--   Differences from the source:
--   - encoding: the conditional probability given $\mathcal R_e=\{f\}$ → the joint form $\text{bound}\cdot\mathbb P[\mathcal R_e=\{f\}]\le\mathbb P[\text{event},\mathcal R_e=\{f\}]$; reason: it agrees with the conditional when the event has positive probability, and it is meaningful at $x_f=0$ and $y=0$
--   - encoding: conditioning on the null event $Y_e=y$ → `atTime`: $Y_e$ is set to the parameter $y$ and the other coordinates are integrated; reason: the $Y_g$ are independent, so this is the regular conditional probability
--   - encoding: the right side of (3) → $s(x_h)\,y\,\tau(zy)$; reason: it equals the printed formula when $zy\ne0$ (proved in a verification file) and is its limit otherwise
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Lemma 2, §3.1, equation (3), p.19; §C.2, ec15–ec16

import Mathlib
import Definitions.Def_RandomOrderCRS_FractionalMatching
import Definitions.Def_RandomOrderCRS_Attenuation
import Definitions.Def_RandomOrderCRS_ArrivalModel
import Definitions.Def_RandomOrderCRS_SimpleBlocker

namespace RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Lemma 2 (First-order minimization), MacRury, Ma & Grammel, arXiv:2209.07520v2, §3.1, equation
(3), p.19, for `a = a₁` and `G` 1-regular: if `f` has vertex `w` not in `e`, then for each
`h ∈ ∂(w) \ {f, fᶜ}`, with `z := 2(1 − x_h) − x_f − x_{fᶜ}`,
`ℙ[sbl_f(h) | ℛ_e = {f}, Y_e = y] ≥ (s(x_h)/z)(1 − (1 − e^{−zy})/(zy))`.

**Formalization Note.** The conditional probability is stated in joint form:
`bound · ℙ[ℛ_e = {f} | Y_e = y] ≤ ℙ[sbl_f(h), ℛ_e = {f} | Y_e = y]`. This agrees with the conditional
when the event has positive probability, and it is meaningful at `x_f = 0` and at `y = 0`. The right
side of (3) is written `s(x_h) y τ(zy)`, which equals it when `zy ≠ 0` and is its limit otherwise.
`Y_e = y` is `atTime`. 1-regularity is the standing assumption of §3. -/
theorem lemma_2 (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (hx : IsOneRegular G x) (e f h : G.edgeSet) (hf : f ∈ edgeNbrs G e)
    (hh : h ∈ blockerCandidates G e f) (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    survival a₁ (x h) * y *
        tau ((2 * (1 - x h) - x f - x (pair (e : Sym2 V) (f : Sym2 V))) * y) *
      arrivalProb G x a₁ (atTime G e y fun Y S => relevantSet G Y S e = {f}) ≤
    arrivalProb G x a₁
      (atTime G e y fun Y S => IsSimpleBlocker G Y S e f h ∧ relevantSet G Y S e = {f}) := by sorry

end RandomOrderCRS
