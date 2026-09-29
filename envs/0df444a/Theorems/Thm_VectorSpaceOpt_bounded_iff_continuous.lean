-- Prove2me | Theorems.Thm_VectorSpaceOpt_bounded_iff_continuous
-- name    : VectorSpaceOpt.bounded_iff_continuous
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T15:48:47.518581+00:00
-- url     : https://prove2.me/theorems/119cbb3f-b501-43ae-a210-fe1f80ac4a1a
-- title:
--   A linear functional is bounded iff it is continuous
-- statement:
--   Let $X$ be a real normed linear space and $f$ a linear functional on $X$. Then $f$ is **bounded** — meaning there is a constant $M$ with
--
--   $$|f(x)| \le M\,\|x\| \qquad \text{for all } x \in X$$
--
--   — **if and only if** $f$ is continuous.
--
--   The equivalence combines two observations. First, a linear functional continuous at a single point is continuous everywhere: linearity translates the behaviour at one point to every other. Second, boundedness and continuity coincide. Bounded implies continuous at the origin, hence everywhere; conversely, continuity at the origin gives a $\delta$ with $|f(x)| < 1$ whenever $\|x\| \le \delta$, and rescaling shows $M = 1/\delta$ bounds $f$.
--
--   The least such $M$ is the **norm** $\|f\|$, and boundedness is not automatic in infinite dimensions: on the space of finitely nonzero sequences under the supremum norm, $f(x) = \sum_k k\,\xi_k$ is linear but unbounded.
--
--   **Formalization Note.** The functional is an unbundled linear map, so that boundedness is a genuine claim rather than part of the type; continuity is topological continuity for the norm topologies. The bound constant is quantified as an arbitrary real, with no sign condition imposed.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §5.2, Propositions 1–2, pp. 104–105

import Mathlib

namespace VectorSpaceOpt

theorem bounded_iff_continuous {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X →ₗ[ℝ] ℝ) :
    (∃ M : ℝ, ∀ x : X, |f x| ≤ M * ‖x‖) ↔ Continuous f := by sorry

end VectorSpaceOpt
