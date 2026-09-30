-- Prove2me | Theorems.Thm_StochasticOrders_MeanResidualLife_dmrl_mrl_order_add_indep
-- name    : StochasticOrders.MeanResidualLife.dmrl_mrl_order_add_indep
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:28:27.159992+00:00
-- url     : https://prove2.me/theorems/9d53c85c-d566-4f4b-8433-d4c38cc84bba
-- title:
--   Theorem 2.A.11 — a DMRL variable is mrl-smaller than itself plus independent noise
-- statement:
--   Let $X$ be a DMRL random variable, and let $Z$ be a nonnegative random variable independent of
--   $X$. Then
--
--   $$X \le_{mrl} X + Z.$$
--
--   This is one of the chapter's closure-property results (§2.A.3): adding independent
--   nonnegative noise to a DMRL random variable can only increase it in the mean residual life
--   order. The book's proof manipulates the survival function of $X+Z$ via convolution and uses
--   the DMRL hypothesis on $X$ at the one step marked in the proof.
--
--   **Formalization Note** $X$ and $Z$ are random variables on the *same* probability space
--   $(\Omega,\mu)$ (unlike `MrlOrder`'s general two-space signature), since the statement's right
--   side is literally the pointwise sum $X+Z$; independence is Mathlib's
--   `ProbabilityTheory.IndepFun X Z μ`. Both $X$ and $Z$ carry explicit `Integrable` hypotheses,
--   formalizing the chapter's standing "finite mean" assumption (needed for both $X$'s mrl
--   function and $X+Z$'s to be the book's genuine conditional expectation rather than the Bochner
--   integral's junk value for a non-integrable summand).
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 87, Theorem 2.A.11

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_mrl
import Definitions.Def_StochasticOrders_MeanResidualLife_MrlOrder
import Definitions.Def_StochasticOrders_MeanResidualLife_DMRL

namespace StochasticOrders.MeanResidualLife

open MeasureTheory ProbabilityTheory

/-- Theorem 2.A.11 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 87): let `X` be
a DMRL random variable with finite mean (the chapter's standing hypothesis, needed for `X`'s and
`X+Z`'s mrl functions to be genuine conditional expectations rather than the Bochner integral's
junk value), and let `Z` be a nonnegative random variable with finite mean independent of `X`.
Then `X ≤mrl X + Z`. -/
theorem dmrl_mrl_order_add_indep {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (hXi : Integrable X μ) (hZi : Integrable Z μ)
    (hDMRL : DMRL μ X) (hZnn : ∀ ω, 0 ≤ Z ω) (hindep : IndepFun X Z μ) :
    MrlOrder μ μ X (fun ω => X ω + Z ω) := by sorry

end StochasticOrders.MeanResidualLife
