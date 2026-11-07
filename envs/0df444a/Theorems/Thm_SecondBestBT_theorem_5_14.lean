-- Prove2me | Theorems.Thm_SecondBestBT_theorem_5_14
-- name    : SecondBestBT.theorem_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:11.494444+00:00
-- url     : https://prove2.me/theorems/8f5682bf-dd39-48ca-bf5a-b4ef7adf6300
-- title:
--   Theorem 5.14 — second-best bilateral trade is $1/2$ efficient
-- statement:
--   Let $F_S$ and $F_B$ be arbitrary independent priors on $[0,\infty)$ with $\mathrm{FB}_{F_S,F_B}<\infty$. Then
--   $$
--   \mathrm{SB}_{F_S,F_B}\ \ge\ \tfrac12\,\mathrm{FB}_{F_S,F_B},
--   $$
--   where $\mathrm{SB}$ is the supremum of the gains from trade over all well-defined mechanisms that are Bayesian incentive compatible and interim individually rational at every type in $[0,\infty)$ and ex-ante weakly budget balanced.
--
--   This is the paper's main lower bound: for every pair of independent nonnegative value distributions, the best incentive-compatible, individually rational, budget-balanced mechanism recovers at least half of the first-best gains from trade. The constant $\frac12$ is tight (Theorem 6.2 of the paper, not part of this mission).
--
--   **Formalization Note** The priors are arbitrary Borel probability measures on $\mathbb R$ concentrated on $[0,\infty)$, with no density, no bounded or finite support and no regularity.
--
--   Differences from the source:
--   - encoding: independent priors $F_S,F_B$ supported on a set $A$ → probability measures on $\mathbb R$ with $\mu(\mathbb R\setminus A)=0$; independence is the product measure; reason: same objects
--   - encoding: $\mathrm{FB}_{F_S,F_B}<\infty$ → integrability of $(b-s)^+$ for $F_S\otimes F_B$; reason: the integrand is nonnegative, so finiteness of its integral is integrability
--   - reading: the paper's BIC and IR for types in $[0,1]$ (Section 2), extended in Appendix A to all $s,b\ge0$ → BIC and IR at every type in $[0,\infty)$; reason: Appendix A extends mechanisms to all nonnegative types; quantifying only over the support would be a larger class and a weaker theorem
--   - encoding: mechanisms $(x,p_B,p_S)$ whose integrals are written without conditions → `WellDefined`: Borel measurable rules, $x\in[0,1]$ on $T\times T$, and finite interim-payment, budget-surplus and GFT integrals; reason: the paper's integrals presuppose these conditions; they only shrink the mechanism class, and the paper's constructions satisfy them
--   - encoding: $\mathrm{SB}$ as a supremum → `sSup` in $\mathbb R$; reason: the feasible GFT set is nonempty and bounded above by $\mathrm{FB}$ (proved in the verification file), so `sSup` is the supremum
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Theorem 5.14, p.24

import Mathlib
import Definitions.Def_SecondBestBT_IsPriorOn
import Definitions.Def_SecondBestBT_secondBest
import Definitions.Def_SecondBestBT_firstBest

open MeasureTheory

namespace SecondBestBT

/-- **Theorem 5.14** (half-approximation guarantee; Liu–Qin–Ren–Wang, *Second-Best Bilateral Trade
is 1/2 Efficient*, arXiv:2606.03849, held version sha256 17184930…, Theorem 5.14, p.24). Let
`F_S` and `F_B` be arbitrary independent priors on `[0, ∞)` with `FB_{F_S,F_B} < ∞`. Then
`SB_{F_S,F_B} ≥ ½ FB_{F_S,F_B}`.

**Formalization Note** The priors are arbitrary Borel probability measures on `ℝ` concentrated on
`[0, ∞)`; independence is the product measure. `FB < ∞` is the integrability of the nonnegative
`(b − s)⁺`. `SB` is the supremum of GFT over well-defined (measurable, integrable) mechanisms that
are BIC and interim IR at every type in `[0, ∞)` and ex-ante WBB. -/
theorem theorem_5_14 (μS μB : Measure ℝ) (hS : IsPriorOn (Set.Ici 0) μS)
    (hB : IsPriorOn (Set.Ici 0) μB)
    (hFB : Integrable (fun p : ℝ × ℝ => max (p.2 - p.1) 0) (μS.prod μB)) :
    1 / 2 * firstBest μS μB ≤ secondBest (Set.Ici 0) μS μB := by sorry

end SecondBestBT
