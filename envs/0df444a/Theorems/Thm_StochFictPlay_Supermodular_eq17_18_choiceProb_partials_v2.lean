-- Prove2me | Theorems.Thm_StochFictPlay_Supermodular_eq17_18_choiceProb_partials_v2
-- name    : StochFictPlay.Supermodular.eq17_18_choiceProb_partials_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:07.473412+00:00
-- url     : https://prove2.me/theorems/2bedeea7-b046-4972-a026-020d2fa14bda
-- title:
--   Eqs. (17)–(18) — sign properties of the derivative of a random utility choice function with a continuous strictly positive shock density
-- statement:
--   Let $C$ be the choice function of a shock density $f$ on $\mathbb R^m$ satisfying the conditions of Theorem 2.1 — $f$ a continuous, finite, everywhere strictly positive probability density whose choice function $C$ is continuously differentiable. Then for every payoff vector $\pi$,
--   $$\text{(17)}\quad \sum_{i=1}^{k} \sum_{j=1}^{l} \frac{\partial C_i}{\partial \pi_j}(\pi) > 0 \ \text{ for all } k, l < m,$$
--   $$\text{(18)}\quad \sum_{j=1}^{m} \frac{\partial C_i}{\partial \pi_j}(\pi) = 0 \ \text{ for all } i \le m.$$
--
--   These are the only two properties of the choice function that the proof of Theorem 5.1 uses; symmetry of $DC$ is not needed for supermodular games.
--
--   **Formalization Note.** The retired version imported a definition of "strictly positive density" asking only for pointwise positivity of one measurable representative, which a density with a genuine zero satisfies after a null-set patch; the resulting smooth $C$ had $DC(0) = 0$ and (17) failed. The new statement is textually the same over the corrected module, in which $f$ is a continuous, finite, strictly positive representative (the version the paper's eq. (4) integrates over hyperplanes, giving strictly negative off-diagonal partials, from which (17) follows via (4)–(5)). Conventions made explicit: strategies are 0-based, so the paper's $k < m$ (1-based) is index $k$ with $k + 1 < m$ and $\sum_{i=1}^k$ is the sum over indices $\le k$; the page leaves $\pi$ implicit and both properties are stated at every $\pi$; $\partial C_i/\partial\pi_j(\pi)$ is the $i$-th entry of the Fréchet derivative of $C$ at $\pi$ applied to the $j$-th basis vector; for $m \le 1$ clause (17) is vacuous.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 30, eqs. (17) and (18), under the hypotheses of Theorem 2.1 (p. 5) read with the regularity of the density used in eq. (4) (p. 6)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel_v2

open scoped ENNReal

namespace StochFictPlay.Supermodular

/-- Equations (17) and (18) (Hofbauer–Sandholm 2002, manuscript p. 30): the two properties of a
random utility choice function `C = choiceProb f` used to prove Theorem 5.1, for a shock density
`f` satisfying the conditions of Theorem 2.1 (`IsRegularDensity`: a continuous, everywhere finite,
strictly positive probability density whose choice function is `C¹`). At every payoff vector
`π ∈ ℝ^m`,

(17) `∑_{i=1}^{k} ∑_{j=1}^{l} ∂C_i/∂π_j (π) > 0` for all `k, l < m`, and

(18) `∑_{j=1}^{m} ∂C_i/∂π_j (π) = 0` for all `i ≤ m`.

Strategies are 0-based: the paper's `k < m` (1-based) is `k.val + 1 < m`, and `∑_{i=1}^{k}` is the
sum over `i ≤ k`. The page leaves the argument `π` implicit; both hold at every `π`.
`∂C_i/∂π_j (π)` is the `i`-th coordinate of the Fréchet derivative of `C` at `π` applied to the
`j`-th basis vector.

Corrected version of `eq17_18_choiceProb_partials`, which imported a definition of
`IsRegularDensity` asking only for pointwise positivity of one measurable version of the density;
a density whose continuous version vanishes at a point was patched on a null set to pass it, and
(17) failed at the resulting critical point of `C`. The statement is unchanged; the fix is in the
imported definition module. -/
theorem eq17_18_choiceProb_partials_v2 (m : ℕ) (f : (Fin m → ℝ) → ℝ≥0∞)
    (hf : IsRegularDensity f) (π : Fin m → ℝ) :
    (∀ k l : Fin m, k.val + 1 < m → l.val + 1 < m →
      0 < ∑ i : Fin m, ∑ j : Fin m,
        (if i ≤ k ∧ j ≤ l then fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i else 0)) ∧
    (∀ i : Fin m, ∑ j : Fin m, fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i = 0) := by sorry

end StochFictPlay.Supermodular
