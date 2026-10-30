-- Prove2me | Theorems.Thm_ShapeSOS_ConvexConsistency_convex_bounds
-- name    : ShapeSOS.ConvexConsistency.convex_bounds
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:24:21.125304+00:00
-- url     : https://prove2.me/theorems/8489a3ae-d6d2-4d4f-9a9a-64e98a7c698c
-- title:
--   Lemma B.6 — all three data-independent convex-regressor bounds
-- statement:
--   Assume the sampling conditions of Assumptions 1–3, with $n\ge1$ and a twice continuously differentiable function $f$ convex on the real box $B$. Fix degree $d$, a best uniform convex approximant $g_d$, and $0<\eta<\min_i(u_i-l_i)/2$. For identifiable samples, let $\bar g_{m,d}$ be an actual least-squares minimizer in (9). There are positive deterministic constants $c_\eta,M_\eta,N_\eta$, independent of the observed data and sample count, such that all three claims hold:
--   $$|\bar g_{m,d}(x)|\le c_\eta\quad\text{a.s. for all }x\in B_{3\eta/4},$$
--   $$|\bar g_{m,d}(x)-\bar g_{m,d}(y)|\le M_\eta\|x-y\|_2\quad\text{a.s. for all }x,y\in B_\eta,$$
--   $$|g_d(x)-g_d(y)|\le N_\eta\|x-y\|_2\quad\text{for all }x,y\in B_\eta.$$
--   The first two assertions apply at each positive sample count, with no eventual-in-sample-size qualification. The first printed bound is false under the permitted Gaussian noise, as recorded in I5.
--
--   Differences from the source:
--   - encoding: real finite-dimensional coordinates and Euclidean geometry → Fin n → ℝ with its usual topology and explicit norm₂ = sqrt(sum x_i²); reason: the topology is the Euclidean topology and all numerical distances use the Euclidean norm
--   - encoding: smoothness on a closed box → ContDiffOn and coordinate fderivWithin on that box; reason: within-domain derivatives preserve the interior derivatives and their continuous boundary values
--   - encoding: Assumptions 1–3 on samples and conditional noise laws → one probability space with an infinite measurable stream, conditional-expectation factorization on every measurable rectangle, and explicit integrability; reason: finite prefixes recover the displayed laws; finite second moments imply the added integrability clauses
--   - reading: full-dimensional interior regions and positive probability on full-dimensional subsets → full-dimensional means nonempty Euclidean interior; probability assertions concern measurable subsets; reason: this is the support interpretation; full affine hull alone would incorrectly force mass on finite affine bases
--   - encoding: named minimizers of the displayed problems → concrete feasible sets, losses, and attained-minimum relations; reason: optimality compares against every feasible polynomial; it is never replaced by a desired asymptotic property
--   - reading: linearly independent feature vectors and sufficiently many data, pp. 4 and 14 footnote 2 → injectivity of evaluation on polynomials of degree at most d; reason: this is full column rank of the regression design; raw feature independence is impossible for growing m
--   - reading: equation (19) indexes coordinate widths by i=1,...,m → all n coordinate widths are used; reason: m denotes the sample count; the widths belong to the n-dimensional box
--   - reading: constants independent of data, with p. 28 explicitly saying not the number of data points → constants precede all positive sample counts and the almost-sure quantifier; reason: preserves uniformity in sample count and never inserts the eventual qualifier from the proof
--   - generalization: Proposition 3.11 describes a smooth function on real n-space → only the required C¹ or C² regularity within the box is imposed; reason: globally smooth source functions specialize to this box-local statement, with the same values and interior derivatives
-- source:
--   Curmei and Hall, Shape-Constrained Regression using Sum of Squares Polynomials, arXiv:2004.03853v3, p. 27, Lemma B.6

import Definitions.Def_ShapeSOS_ConvexConsistency_Sampling

set_option autoImplicit false
open Filter MeasureTheory
open scoped BigOperators Topology MeasureTheory

namespace ShapeSOS.ConvexConsistency

theorem convex_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (B : Box n) (f : Vec n → ℝ) (X : ℕ → Ω → Vec n) (ν : ℕ → Ω → ℝ)
    (hs : SamplingAssumptions μ B f X ν)
    (hf : ContDiffOn ℝ 2 f B.carrier) (hcv : ConvexOn ℝ B.carrier f)
    (d : ℕ) (gd : Poly n) (hg : Minimizes (convexClass B d) (approximationLoss B f) gd)
    (η : ℝ) (hη : B.validInset η) :
    (∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 0 < m →
      ∀ᵐ ω ∂μ, Identifiable m d (fun i => X i ω) → ∀ p : Poly n,
        Minimizes (convexClass B d)
          (empiricalLoss m (fun i => X i ω) (fun i => response f X ν i ω)) p →
        ∀ x ∈ B.inner (3 * η / 4), |value p x| ≤ c) ∧
    (∃ M : ℝ, 0 < M ∧ ∀ m : ℕ, 0 < m →
      ∀ᵐ ω ∂μ, Identifiable m d (fun i => X i ω) → ∀ p : Poly n,
        Minimizes (convexClass B d)
          (empiricalLoss m (fun i => X i ω) (fun i => response f X ν i ω)) p →
        ∀ x ∈ B.inner η, ∀ y ∈ B.inner η,
          |value p x - value p y| ≤ M * norm₂ (x-y)) ∧
    (∃ N : ℝ, 0 < N ∧ ∀ x ∈ B.inner η, ∀ y ∈ B.inner η,
      |value gd x - value gd y| ≤ N * norm₂ (x-y)) := by sorry

end ShapeSOS.ConvexConsistency
