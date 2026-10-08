-- Prove2me | Theorems.Thm_SSPAnalysis_Bellman_equation22
-- name    : SSPAnalysis.Bellman.equation22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:10:57.517961+00:00
-- url     : https://prove2.me/theorems/c1918769-52a7-44ce-bb64-23c5e1dfc631
-- title:
--   Appendix equation (22) — inverse formula for proper-policy costs
-- statement:
--   Let $\mu$ be proper under Assumption 1. Let $I$ be the identity matrix and let $E$ have every entry in its first column equal to one and all other entries zero. Then $I-P(\mu)+E$ is invertible and
--
--   $$x(\mu)=(I-P(\mu)+E)^{-1}c(\mu).$$
--
--   The formula turns the cost of a proper policy into a finite linear-system solution. The Appendix uses it in Lemma 3(a).
--
--   **Formalization Note.** Matrix invertibility is asserted explicitly; the paper derives it just before equation (22). The cost equality casts the resulting real coordinate into extended reals. State $1$ is `0 : Fin n`; no Assumption 2 is used.
-- source:
--   Bertsekas and Tsitsiklis, An Analysis of Stochastic Shortest Path Problems, Math. Oper. Res. 16(3) (1991), p. 591, Appendix, equation (22) and the preceding invertibility claim

import Mathlib
import Definitions.Def_SSPAnalysis_Bellman_SSP

namespace SSPAnalysis.Bellman

open Matrix Filter Topology

/-- Appendix equation (22) (p. 591): the proper-policy cost is the
solution of the nonsingular augmented linear system. -/
theorem equation22 {n : ℕ} [NeZero n] {U : Fin n → Type*}
    (m : Model n U) (h1 : m.Assumption1) :
    ∀ μ : Selector U, m.IsProper μ →
      IsUnit (1 - m.P μ + E) ∧
      ∀ i, m.cost (stationary μ) i =
        (((1 - m.P μ + E)⁻¹ *ᵥ m.cvec μ) i : EReal) := by sorry

end SSPAnalysis.Bellman
