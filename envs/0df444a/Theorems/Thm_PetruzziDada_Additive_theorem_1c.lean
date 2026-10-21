-- Prove2me | Theorems.Thm_PetruzziDada_Additive_theorem_1c
-- name    : PetruzziDada.Additive.theorem_1c
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:11.090594+00:00
-- url     : https://prove2.me/theorems/d5ae31e3-7a3f-4a50-ab72-e2db83898b6b
-- title:
--   Theorem 1(c) — if 2r(z)² + r′(z) > 0 and a − b(c − 2s) + A > 0, z* is the unique root of dE[Π(z, p(z))]/dz in [A, B]
-- statement:
--   Consider the additive-demand price-setting newsvendor: demand $a - bp + \varepsilon$ with $a > 0$, $b > 0$; the noise $\varepsilon$ has a density $f$ on $[A,B]$, $A > -a$, with distribution function $F$; unit stocking cost $c$, unit disposal cost $h \ge -c$, unit shortage penalty $s$. Stocking $q = y(p) + z$ units at price $p$ earns expected profit $E[\Pi(z,p)]$ (the integral of p. 184), and $p(z) = p^0 - \Theta(z)/2b$ is the optimal price for a fixed $z$ (Lemma 1). Let $r(z) = f(z)/[1-F(z)]$ be the hazard rate. Suppose
--   $$2r(z)^2 + \frac{dr(z)}{dz} > 0 \quad (A \le z < B) \qquad\text{and}\qquad a - b(c-2s) + A > 0.$$
--   Then there is $z^* \in [A,B]$ such that $z^*$ is the **unique** $z \in [A,B]$ satisfying
--   $$\frac{dE[\Pi(z,p(z))]}{dz} = 0,$$
--   and stocking $q^* = y(p^*) + z^*$ units at price $p^* = p(z^*)$ is optimal:
--   $$E[\Pi(z,p)] \le E[\Pi(z^*,p(z^*))] \quad\text{for all } z \in [A,B] \text{ and all } p \in \mathbb R.$$
--
--   This is Theorem 1(c) of Petruzzi and Dada. It says that under a hazard-rate condition weaker than an increasing failure rate, the joint pricing and stocking problem is solved by the first-order condition alone, which generalizes the results of Ernst (1970) and Young (1978).
--
--   **Formalization Note** The hazard condition is required on $[A,B)$ rather than $[A,B]$ because $F(B) = 1$ makes $r(B)$ undefined; at each such $z$ the derivative of $r$ relative to $[A,B]$ (one-sided at $A$) is required to exist. The derivative $dE[\Pi(z,p(z))]/dz$ is Mathlib's `deriv`; the reduced objective is differentiable everywhere, so it is the genuine derivative. "$z^*$ is determined" is rendered as optimality over $z \in [A,B]$ and every real price, against the integral objective.
-- source:
--   Petruzzi & Dada, Pricing and the Newsvendor Problem: A Review with Extensions, Oper. Res. 47(2) 1999, p. 185, Theorem 1(c)

import Mathlib
import Definitions.Def_PetruzziDada_Additive_Model

open MeasureTheory

namespace PetruzziDada.Additive

/-- Theorem 1(c), p. 185: if `2r(z)² + dr(z)/dz > 0` and `a - b(c - 2s) + A > 0`, then `z*`
is the unique `z ∈ [A, B]` with `dE[Π(z, p(z))]/dz = 0`, and stocking `q* = y(p*) + z*` at
`p* = p(z*)` is optimal for (4) over `z ∈ [A, B]` and every real price `p`. -/
theorem theorem_1c (M : Model) (hr : M.HazardCondition)
    (hpos : 0 < M.a - M.b * (M.c - 2 * M.s) + M.A) :
    ∃ zstar ∈ Set.Icc M.A M.B,
      {z ∈ Set.Icc M.A M.B | deriv M.reducedProfit z = 0} = {zstar} ∧
        ∀ z ∈ Set.Icc M.A M.B, ∀ p : ℝ, M.expProfit z p ≤ M.expProfit zstar (M.price zstar) := by sorry
end PetruzziDada.Additive
