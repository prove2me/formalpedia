-- Prove2me | Theorems.Thm_ParallelLpSCO_EpochDA_lemma_21
-- name    : ParallelLpSCO.EpochDA.lemma_21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:05:05.834064+00:00
-- url     : https://prove2.me/theorems/1ea7e05d-bbd7-4096-8cff-231efad6f7ec
-- title:
--   Lemma 21 — a ball-oracle output is within $r/(3C_{ba})$ of the prox point w.p. $\ge 2/3$; $\lceil20\log(1/\zeta)\rceil$ repetitions and Aggregate give $r/C_{ba}$ w.p. $\ge1-\zeta$
-- statement:
--   Let $F$ be convex, $X$ closed and convex, $\bar x\in X$, $\lambda>0$, and let $x^\star_{\bar x,\lambda}$ minimize $F(x)+\frac\lambda p\|x-\bar x\|_p^p$ over $X\cap B_p(\bar x,r)$. Suppose a $\big(\frac{2^{2-p}\lambda r^p}{p\,3^{p+1}C_{ba}^p},\lambda\big)$-ball optimization oracle returns $x\in X\cap B_p(\bar x,r)$. Then
--   $$\Pr\Big(\|x-x^\star_{\bar x,\lambda}\|_p\le\frac r{3C_{ba}}\Big)\ge\frac23.\qquad(40)$$
--   Moreover, let $x_1,\dots,x_m$ be $m=\lceil20\log(1/\zeta)\rceil$ independent outputs of the oracle. With probability at least $1-\zeta$, at least $0.51m$ of them satisfy $\|x_i-x^\star_{\bar x,\lambda}\|_p\le r/(3C_{ba})$. Consequently Aggregate (Algorithm 11) applied to them returns $\hat x$ with $\|\hat x-x^\star_{\bar x,\lambda}\|_p\le r/C_{ba}$ with probability at least $1-\zeta$.
--
--   This turns an in-expectation ball oracle into a high-probability distance test, which is what NextLambda needs inside ball acceleration.
--
--   **Formalization Note.** Probabilities are values of the probability measure `P` in $[0,\infty]$; Aggregate is run with radius $r/C_{ba}$.
--
--   Differences from the source:
--   - reading: x⋆_{x̄,λ} (undefined on the page) → a minimizer of F + (λ/p)‖· − x̄‖_p^p over X ∩ B_p(x̄, r) (IsBallProx); reason: Propositions 11–12: local minimization is over X ∩ B_p(x̄, r)
--   - reading: x̄ ∈ X, F, X, C_ba from the context of §4.1 and Proposition 11 → F convex on ℝ^d, X closed and convex (Assumption 1), C_ba any positive constant; reason: the lemma's proof uses only these properties; C_ba is a free constant of Proposition 11
--   - reading: m independent outputs of the ball optimization oracle; ζ unrestricted, log unspecified → m = ⌈20 log(1/ζ)⌉ independent random points, each in X ∩ B_p(x̄, r) and each meeting the oracle guarantee, for ζ ∈ (0, 1), natural log; reason: a probability bound 1 − ζ is meaningful for ζ ∈ (0, 1); the oracle may be randomized differently on each call
--   - encoding: the oracle guarantee E[F(x) + (λ/p)‖x − x̄‖_p^p] ≤ F(x⋆) + (λ/p)‖x⋆ − x̄‖_p^p + ϕ (Definition 7) → BallOracleGuarantee: the random variable is integrable and its Bochner integral satisfies the bound; the random points are measurable; reason: the source takes the expectation to exist and the outputs to be random variables; Lean's integral of a non-integrable function is 0
-- source:
--   Nie, Shyam, Bullins, Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in ℓp Geometries, STOC 2027 submission (manuscript, sha256 fe68639b…), pp. 49–50, Lemma 21

import Mathlib
import Definitions.Def_ParallelLpSCO_EpochDA_Basics
import Definitions.Def_ParallelLpSCO_EpochDA_Algorithms

open MeasureTheory

namespace ParallelLpSCO.EpochDA

/-- Lemma 21 (pp. 49–50). Let `F` be convex, `X` closed convex, `x̄ ∈ X`, `λ, r, C_ba > 0`, and
`x⋆` the minimizer of `F + (λ/p)‖· − x̄‖_p^p` over `X ∩ B_p(x̄, r)`. An output `x ∈ X ∩ B_p(x̄, r)`
of a `(2^{2−p} λ r^p / (p 3^{p+1} C_ba^p), λ)`-ball optimization oracle is within `r/(3C_ba)` of
`x⋆` with probability at least `2/3`; for `m = ⌈20 log(1/ζ)⌉` independent such outputs, with
probability at least `1 − ζ` at least `0.51m` of them are, and Aggregate with radius `r/C_ba`
returns a point within `r/C_ba` of `x⋆`. -/
theorem lemma_21 (p : ℝ) (hp : 2 ≤ p) (d : ℕ) (F : Vec d → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (X : Set (Vec d)) (hXc : IsClosed X) (hX : Convex ℝ X) (xbar : Vec d) (hxbar : xbar ∈ X)
    (lam r Cba : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hC : 0 < Cba) (xstar : Vec d)
    (hxstar : IsBallProx p F X r lam xbar xstar) :
    let phi : ℝ := (2 : ℝ) ^ (2 - p) * lam * r ^ p / (p * (3 : ℝ) ^ (p + 1) * Cba ^ p)
    (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (x : Ω → Vec d),
      Measurable x → (∀ ω, x ω ∈ X ∩ lpBall p xbar r) →
      BallOracleGuarantee p F lam phi xbar xstar P x →
      ENNReal.ofReal (2 / 3) ≤ P {ω | lpNorm p (x ω - xstar) ≤ r / (3 * Cba)}) ∧
    (∀ ζ : ℝ, 0 < ζ → ζ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (xs : Fin ⌈20 * Real.log (1 / ζ)⌉₊ → Ω → Vec d),
        (∀ i, Measurable (xs i)) → ProbabilityTheory.iIndepFun xs P →
        (∀ i ω, xs i ω ∈ X ∩ lpBall p xbar r) →
        (∀ i, BallOracleGuarantee p F lam phi xbar xstar P (xs i)) →
        ENNReal.ofReal (1 - ζ) ≤
            P {ω | (51 / 100 : ℝ) * (⌈20 * Real.log (1 / ζ)⌉₊ : ℝ) ≤
              ((Finset.univ.filter fun i => lpNorm p (xs i ω - xstar) ≤ r / (3 * Cba)).card : ℝ)} ∧
          ENNReal.ofReal (1 - ζ) ≤
            P {ω | ∃ i, aggregate p (fun j => xs j ω) (r / Cba) = some i ∧
              lpNorm p (xs i ω - xstar) ≤ r / Cba}) := by sorry

end ParallelLpSCO.EpochDA
