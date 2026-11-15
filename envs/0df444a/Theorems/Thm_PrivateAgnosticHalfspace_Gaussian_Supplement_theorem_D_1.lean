-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_Supplement_theorem_D_1
-- name    : PrivateAgnosticHalfspace.Gaussian.Supplement.theorem_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:09:54.025212+00:00
-- url     : https://prove2.me/theorems/c1335187-131c-4647-b930-79774ee36214
-- title:
--   Theorem D.1 — private agnostic learning for known log-concave marginals
-- statement:
--   There are universal constants $C,R_0,A,B>0$, $c\in(0,1/4]$, fixed natural exponents and one sample-only optimizer and learner program, chosen before all learning instances. Let $\alpha,\beta\in(0,1)$ and $\varepsilon,\delta\in(0,1/2]$. Let $\mu$ be any known full-dimensional log-concave marginal on $\mathbb R^d$, and let $P$ have marginal $\mu$ and arbitrary conditional binary labels. Set $p=\lceil\exp(C/\alpha)\rceil$, $D_p=\binom{d+p}{p}$ and let $T$ be the exact minimum in (22). The modified Algorithm 1 is $(\varepsilon,\delta)$-DP for every deterministic input dataset, and
--   $$\Pr\{\operatorname{err}_P(h)\le\operatorname{OPT}+\alpha\}\ge1-\beta,\qquad n\le A\left(\frac{D_p}{\alpha^2}+\frac{T\sqrt{D_p}}{\varepsilon\alpha}\right)\Lambda^r.$$
--   Here $\Lambda=1+\log(1/\alpha)+\log(1/\beta)+\log(1/\varepsilon)+\log(1/\delta)$. The theorem establishes finiteness of all monomial moments, positive definiteness of the Gram matrix, measurable orthonormal polynomial features spanning the full degree cutoff, attainment of the positive minimum, and
--   $$\frac34\le T\le\sqrt{\frac{D_p}{c\alpha}},\qquad n\le A\left(\frac{D_p}{\alpha^2}+\frac{D_p}{\varepsilon\alpha^{3/2}}\right)\Lambda^r.$$
--   The latter is a consequence; it does not replace the marginal-dependent bound. The output coefficients lie in the radius-$R_0$ ball and its threshold lies in $[-1,1]$.
--
--   If concrete public routines construct the orthonormal polynomial basis and compute $T$ in at most $Q(D_p+1)^u$ operations, the complete pipeline, including that preprocessing and basis evaluation on each example, realizes the same learner in at most $B(Q+1)(n+1)^{s+u}$ charged operations. This condition affects runtime only. Neither privacy nor accuracy assumes a computational certificate, population conditional labels, or an optimal halfspace.
--
--   **Formalization Note** The proof writes O/soft-O and yields uniform constants, not numerical values. The exact public schedule takes $k=\lceil\log_2(2/\beta)\rceil$, $M=\lceil C_s/\alpha\rceil$, the least $n_0\ge2$ satisfying (27), and $m=\lceil C_s(\alpha^{-2}+(\varepsilon\alpha)^{-1})\log(kM/\beta)\rceil$, with $n=kn_0+m$. The statement also gives the explicit ceiling upper bound on $n_0$ from the brief. Equivalent moment Gram–Schmidt is the source-permitted orthonormal-basis choice. The raw density can vanish; no isotropy, bounded support, smoothness or extra label condition is introduced.
--
--   Differences from the source:
--   - encoding: Euclidean examples with labels ±1, affine thresholds, and positive integer dimension → EuclideanSpace over Fin d with d ≥ 1, Borel measures, Bool labels decoded as ±1, sign(0)=+1; reason: coordinate and label encodings preserve all source instances; all real affine thresholds remain allowed
--   - encoding: known full-dimensional log-concave density exp(-V), allowing convex supports → the published nonnegative power-form log-concavity predicate, a density measure and exclusion of affine-hyperplane concentration; reason: equivalent density formulation permits zeros, with V=-log f on its positive set and +infinity elsewhere; it adds no positivity, smoothness or isotropy requirement
--   - reading: inverse-square-root Gram features or an equivalent orthonormal polynomial basis, pp.28–29 → lexicographic moment Gram–Schmidt coefficients and the corresponding actual polynomial features; reason: this is the expressly permitted equivalent public basis; its pointwise feature norm and hence the exact threshold (22) are invariant under the orthogonal basis change
--   - encoding: positive minimum threshold (22) and the integer schedule (27) → real infimum together with an IsLeast conclusion, explicit positive bounds, least feasible integer training size and rounded validation; reason: attainment, integrability, normalization and feasibility are conclusions, never assumed certificates or default-zero successes
--   - reading: polynomial arithmetic runtime provided public feature construction, evaluation and T computation take poly(Dp) → concrete public basis/T code with finite public input and charged preprocessing plus the uniform sample-only learner code; reason: pins down the conditional computation claim; the polynomial feature matrix gives polynomial evaluation, and the public input and routines are fixed independently of conditional labels
--   - generalization: the theorem statement on p.28 → additional conclusions: finite moments, positive-definite Gram matrix, measurable orthonormal spanning features with norm at least 1, attainment of (22) with 3/4 ≤ T ≤ sqrt(Dp/(cα)), the explicit n0 bound, the worst-case sample bound Dp/α²+Dp/(εα^{3/2}), and outputs inside the radius-R0 ball with threshold in [-1,1]; reason: each is stated in the text on pp.28–31 (construction, Remark 3 and (7), T ≥ 3/4 on p.31, the sample consequence after the theorem); dropping the extra conjuncts gives exactly the printed theorem
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, Privacy for Free in Efficient Agnostic Halfspace Learning, STOC 2027 submission #1006 (October 2026), canonical held submission (not a proceedings-acceptance claim), pp.28–31, Theorem D.1, Appendix D.1, Eqs. (22),(27),(28)

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Supplement_LogConcave

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian.Supplement

/-- Theorem D.1 (pp.28--31): full known log-concave marginal result. Existence of the
orthonormal features, the attained positive threshold and all schedules are conclusions.
Only the runtime clause uses polynomial public construction routines. -/
theorem theorem_D_1 :
    ∃ (c : MarginalConstants) (O : MarginalOptimizer) (code : Code)
      (A B : ℝ) (r s : ℕ),
      1 ≤ c.degree ∧ 0 < c.accuracy ∧ c.accuracy ≤ 1 / 4 ∧
      1 ≤ c.coefficientRadius ∧ 1 ≤ c.schedule ∧ 0 < A ∧ 0 < B ∧
      ∀ d : ℕ, 1 ≤ d → ∀ α β ε δ : ℝ,
      0 < α → α < 1 → 0 < β → β < 1 →
      0 < ε → ε ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 2 →
      ∀ μ : Measure (Vec d), IsLogConcaveMarginal d μ → FullDimensional d μ →
      let p := marginalDegree c α
      let D := featureDimension d p
      let φ := marginalFeatures d p μ
      let T := marginalThreshold d p μ c.accuracy α
      let n₀ := marginalTrainingSize c d p T α ε δ
      let n := marginalSize c d p T α β ε δ
      (∀ κ : Fin d → ℕ, Integrable (fun x : Vec d => ∏ i, x i ^ κ i) μ) ∧
      (gram d p μ).PosDef ∧ Measurable φ ∧
      (∀ i j : Index d p, Integrable (fun x => φ x i * φ x j) μ ∧
        ∫ x, φ x i * φ x j ∂μ = if i = j then 1 else 0) ∧
      (∀ f ∈ polynomialFunctions d p, ∃ v : Coeff d p, ∀ x, f x = inner ℝ v (φ x)) ∧
      (∀ x, 1 ≤ ‖φ x‖) ∧
      IsLeast (thresholds22 d p μ c.accuracy α) T ∧
      3 / 4 ≤ T ∧ T ≤ Real.sqrt (D / (c.accuracy * α)) ∧
      marginalCondition c d p T α ε δ n₀ ∧
      (n₀ : ℝ) ≤ 3 + 4 * c.schedule ^ 2 * c.coefficientRadius ^ 2 * D /
        (c.accuracy ^ 2 * α ^ 2) + 2 * c.schedule * c.coefficientRadius * T *
        Real.sqrt (D * Real.log (1 / δ)) / (c.accuracy * ε * α) ∧
      (n : ℝ) ≤ A * (D / α ^ 2 + T * Real.sqrt D / (ε * α)) * logs α β ε δ ^ r ∧
      (n : ℝ) ≤ A * (D / α ^ 2 + D / (ε * α ^ (3 / 2 : ℝ))) * logs α β ε δ ^ r ∧
      ∃ L : PrivateUniformGen.Characterization.Mechanism (Example d) (MarginalOutput d p) n,
        Realizes (marginalLaw O c d p φ T α β ε δ) L ∧
        PrivateUniformGen.Characterization.IsDP L ε δ ∧
        (∀ S, (L S : Measure (MarginalOutput d p))
          {o | ‖o.1‖ ≤ c.coefficientRadius ∧ |o.2| ≤ 1} = 1) ∧
        (∀ P : Measure (Example d), IsProbabilityMeasure P → P.map Prod.fst = μ →
          Accurate L (marginalDecode (fun x => radial T (φ x))) P (opt d P + α) β) ∧
        (∀ (build threshold : Code) (info : List ℝ) (Q : ℝ) (u : ℕ), 1 ≤ Q →
          PublicComputes build threshold info d p (basisMatrix d p μ) T α Q u →
          let budget := ⌊B * (Q + 1) * (n + 1 : ℝ) ^ (s + u)⌋₊
          let preBudget := ⌊Q * (D + 1 : ℝ) ^ u⌋₊
          ∀ S : Fin n → Example d,
            ImplementsMarginal code build threshold info (budget + 1) budget d p
              (marginalInput c d p (basisMatrix d p μ) T α β ε δ (List.ofFn S))
              α preBudget (L S : Measure (MarginalOutput d p))) := by sorry

end PrivateAgnosticHalfspace.Gaussian.Supplement
