-- Prove2me | Theorems.Thm_ShapeSOS_ConvexConsistency_consistency
-- name    : ShapeSOS.ConvexConsistency.consistency
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:25:12.744699+00:00
-- url     : https://prove2.me/theorems/fc000f4d-b2ba-42ce-a254-a0d61b83f358
-- title:
--   Theorem 3.9 — printed almost-sure consistency at every fixed SOS hierarchy level
-- statement:
--   Let $n\ge1$, let $B=\prod_i[l_i,u_i]\subset\mathbb R^n$ with real $l_i<u_i$, and let $C\subseteq B$ be closed with nonempty interior and $C\cap\partial B=\varnothing$. Let $f$ be twice continuously differentiable and convex on $B$. On one probability space, observe prefixes of $Y_i=f(X_i)+\nu_i$ satisfying Assumptions 1–3: iid covariates supported throughout $B$ with finite second moment, full real support noise with common finite second moment, conditional mean zero, and the displayed conditional product law. The noise laws need not be identical or independent of the covariates.
--
--   For every fixed $r\in\mathbb N$, including zero, and every deterministic schedule $m(d)\to\infty$, choose the actual polynomial least-squares estimator from (3), with a fixed deterministic choice among ties. The source asserts
--   $$\sup_{x\in C}|\tilde g_{m(d),d,r}(x)-f(x)|\longrightarrow0\quad\text{almost surely as }d\to\infty.$$
--   The formal conclusion also asserts, almost surely, that the selected estimator is an attained optimizer for all sufficiently large $d$. The selector's zero value outside the attained domain gives no optimality and cannot discharge this conclusion. The degree caps are exactly $2r$ and $2r-2$, and no growth condition beyond $m(d)\to\infty$ is imposed. The false fixed-$r$ claim remains the target; I1 records its counterexample.
--
--   Differences from the source:
--   - encoding: real finite-dimensional coordinates and Euclidean geometry → Fin n → ℝ with its usual topology and explicit norm₂ = sqrt(sum x_i²); reason: the topology is the Euclidean topology and all numerical distances use the Euclidean norm
--   - encoding: smoothness on a closed box → ContDiffOn and coordinate fderivWithin on that box; reason: within-domain derivatives preserve the interior derivatives and their continuous boundary values
--   - encoding: Assumptions 1–3 on samples and conditional noise laws → one probability space with an infinite measurable stream, conditional-expectation factorization on every measurable rectangle, and explicit integrability; reason: finite prefixes recover the displayed laws; finite second moments imply the added integrability clauses
--   - reading: full-dimensional interior regions and positive probability on full-dimensional subsets → full-dimensional means nonempty Euclidean interior; probability assertions concern measurable subsets; reason: this is the support interpretation; full affine hull alone would incorrectly force mass on finite affine bases
--   - encoding: certificate caps 2r and 2r−2, including r=0 → integer degree caps, permitting only the zero polynomial under negative caps; reason: natural subtraction would erroneously permit nonzero constants at negative degree
--   - reading: d,m:=m(d)→∞ and lim_{d,m→∞} → every deterministic schedule m(d) tending to infinity; reason: uses the stronger schedule interpretation, without an existence-of-schedule or sufficiently-fast restriction
--   - encoding: the estimator named by argmin → a deterministic classical choice from actual minimizers, zero only when none exist; reason: fixes ties without adding a model axiom or changing any attained-domain instance
--   - generalization: existence implicit in the named estimator and the assertion for large sample sizes → eventual attained optimality is an explicit conjunct of the almost-sure conclusion; reason: adds the implicit existence guarantee rather than assuming it, and prevents a default value from making the theorem true
-- source:
--   Curmei and Hall, Shape-Constrained Regression using Sum of Squares Polynomials, arXiv:2004.03853v3, p. 13, Theorem 3.9

import Definitions.Def_ShapeSOS_ConvexConsistency_Sampling

set_option autoImplicit false
open Filter MeasureTheory
open scoped BigOperators Topology MeasureTheory

namespace ShapeSOS.ConvexConsistency

theorem consistency {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (B : Box n) (C : Set (Vec n)) (hC : InteriorRegion B C)
    (f : Vec n → ℝ) (hf : ContDiffOn ℝ 2 f B.carrier) (hconvex : ConvexOn ℝ B.carrier f)
    (X : ℕ → Ω → Vec n) (ν : ℕ → Ω → ℝ) (hs : SamplingAssumptions μ B f X ν)
    (r : ℕ) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    ∀ᵐ ω ∂μ,
      (∀ᶠ d in atTop, Minimizes (convexSOSFeasible B d r)
        (empiricalLoss (m d) (fun i => X i ω) (fun i => response f X ν i ω))
        (convexSOSE B (m d) d r (fun i => X i ω) (fun i => response f X ν i ω))) ∧
      Tendsto (fun d => uniformError C
        (value (convexSOSE B (m d) d r (fun i => X i ω) (fun i => response f X ν i ω))) f)
        atTop (𝓝 0) := by sorry

end ShapeSOS.ConvexConsistency
