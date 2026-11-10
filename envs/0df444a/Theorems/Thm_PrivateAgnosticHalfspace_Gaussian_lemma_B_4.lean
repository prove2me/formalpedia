-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_4
-- name    : PrivateAgnosticHalfspace.Gaussian.lemma_B_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:24:34.183777+00:00
-- url     : https://prove2.me/theorems/1bc1d313-4e9b-47d8-a3db-0a225fc50cad
-- title:
--   Lemma B.4 — private convex ERM, including oracle cost
-- statement:
--   There is a universal constant $A>0$ and a uniform real arithmetic oracle program with the following guarantee. Let $\Omega\subseteq\mathbb R^D$ be public, nonempty, compact and convex, with Euclidean diameter $R$. Let the public loss $\ell(\cdot;z)$ be convex and $T$-Lipschitz on all of $\mathbb R^D$ for each example $z$, with $T\ge0$. For $n\ge2$ and $\varepsilon,\delta\in(0,1/2]$, the program has an $(\varepsilon,\delta)$-DP output law $M$ under replacement adjacency. On every dataset and every random tape its output belongs to $\Omega$, and
--   $$
--   \mathbb E\left[\widehat L_S(\widehat v)-\min_{v\in\Omega}\widehat L_S(v)\right]
--   \le A\frac{TR\sqrt{D\log(1/\delta)}}{n\varepsilon}.
--   $$
--   The program makes at most $An^2$ subgradient evaluations and at most $An^2$ Euclidean projections. The same program is chosen before the dimension, domain, loss, privacy parameters and dataset. Valid oracle selections, an initial feasible point, termination, output-law measurability and integrability of the excess loss are conclusions.
--
--   This is the private optimization component used in each independent training block. The paper writes $O(\cdot)$; its proof on p.21 supplies universal constants for the excess loss and both oracle counts, combined here into one universal $A$.
--
--   Differences from the source:
--   - encoding: Euclidean vectors and a nonnegative Lipschitz bound → EuclideanSpace coordinates and T : nonnegative real; reason: the underlying Euclidean instances are unchanged
--   - encoding: a private algorithm with expected loss and O(n²) oracle counts → an existential uniform oracle program, probability laws and charged execution; reason: makes sample-only computation, normalization and oracle counting explicit without assuming success
--   - encoding: the minimum on the nonempty compact feasible set → sInf of the empirical-loss image, with compactness and global Lipschitz hypotheses; reason: the continuous empirical objective attains its minimum; the explicit excess-loss integrability prevents a default integral
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, STOC 2027 submission #1006 (October 2026), p. 21, Lemma B.4; canonical PDF sha256 f0122a33e29daa624b530bdd0b071998d8e44197b30449b0cb3213289645cec7

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian

/-- Lemma B.4, p.21, including an operational oracle-call bound.
One finite real arithmetic program is fixed before every optimization instance. -/
theorem lemma_B_4 :
    ∃ (A : ℝ) (code : Program), 0 < A ∧
    ∀ (D : ℕ) (Z : Type*) (Ω : Set (Vec D)) (ℓ : Vec D → Z → ℝ)
      (R : ℝ) (T : ℝ≥0),
      Ω.Nonempty → IsCompact Ω → Convex ℝ Ω → Metric.diam Ω = R →
      (∀ z, ConvexOn ℝ Set.univ (fun v => ℓ v z)) →
      (∀ z, LipschitzWith T (fun v => ℓ v z)) →
      ∀ (n : ℕ), 2 ≤ n → ∀ (ε δ : ℝ),
      0 < ε ∧ ε ≤ 1 / 2 → 0 < δ ∧ δ ≤ 1 / 2 →
      ∃ (x₀ : Vec D) (g : Z → Vec D → Vec D) (π : Vec D → Vec D) (fuel : ℕ)
        (M : PrivateUniformGen.Characterization.Mechanism Z (Vec D) n),
        x₀ ∈ Ω ∧ IsSubgradient D ℓ g ∧ IsProjection D Ω π ∧
        PrivateUniformGen.Characterization.IsDP M ε δ ∧
        ∀ S : Fin n → Z,
          (∀ ω, ∃ s, execute code (sampleOracle D g π S) (ermInput D n ε δ R T x₀) ω fuel {} = some s ∧
            (s.gradients : ℝ) ≤ A * n ^ 2 ∧ (s.projections : ℝ) ≤ A * n ^ 2 ∧
            readVector D s.registers 0 ∈ Ω) ∧
          let out := fun ω => match execute code (sampleOracle D g π S)
              (ermInput D n ε δ R T x₀) ω fuel {} with
            | none => 0
            | some s => readVector D s.registers 0
          Measurable out ∧ (M S : Measure (Vec D)) = tapeLaw.map out ∧
          Integrable (fun v => generalEmpiricalLoss D ℓ S v - empiricalMinimum D ℓ S Ω)
            (M S : Measure (Vec D)) ∧
          (∫ v, generalEmpiricalLoss D ℓ S v - empiricalMinimum D ℓ S Ω ∂(M S : Measure (Vec D))) ≤
            A * T * R * Real.sqrt ((D : ℝ) * Real.log (1 / δ)) / (n * ε) := by sorry

end PrivateAgnosticHalfspace.Gaussian
