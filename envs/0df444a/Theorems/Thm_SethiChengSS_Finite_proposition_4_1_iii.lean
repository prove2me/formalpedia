-- Prove2me | Theorems.Thm_SethiChengSS_Finite_proposition_4_1_iii
-- name    : SethiChengSS.Finite.proposition_4_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:46.361202+00:00
-- url     : https://prove2.me/theorems/19d2964f-0945-4c88-a1b6-31b6858b0874
-- title:
--   Proposition 4.1(iii), p. 934 — if g is K-convex and E|g(x − ξ)| < ∞, then E g(x − ξ) is K-convex
-- statement:
--   Let $g$ be $K$-convex, $K \ge 0$, and let $\xi$ be a real random variable with law $\mu$ such that $E|g(x-\xi)| < \infty$ for every $x$. Then
--   $$x \longmapsto E\,g(x - \xi) = \int g(x - z)\,\mu(dz)$$
--   is $K$-convex.
--
--   This is the step that carries $K$-convexity of $v_{n+1}$ through the demand of period $n$ in (3.1).
--
--   **Formalization Note** The random variable is represented by its law, a probability measure on $\mathbb R$, and integrability is assumed at every $x$. The published `BertsekasDP.kconvex_expectation` covers only finitely supported $\xi$.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 934, Proposition 4.1(iii)

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Finite_KConvexity
open MeasureTheory Filter Topology

namespace SethiChengSS.Finite

/-- Proposition 4.1(iii) (Sethi–Cheng 1997, p. 934): if `g` is `K`-convex and `ξ` is a random
variable (law `μ`) with `E|g(x − ξ)| < ∞` for every `x`, then `x ↦ E g(x − ξ)` is `K`-convex. -/
theorem proposition_4_1_iii (K : ℝ) (g : ℝ → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hK : 0 ≤ K) (hg : BertsekasKConvex K g) (hint : ∀ x, Integrable (fun z => g (x - z)) μ) :
    BertsekasKConvex K (fun x => ∫ z, g (x - z) ∂μ) := by sorry

end SethiChengSS.Finite
