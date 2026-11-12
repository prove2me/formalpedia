-- Prove2me | Theorems.Thm_ParallelLpSCO_EpochDA_proposition_13
-- name    : ParallelLpSCO.EpochDA.proposition_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:05:22.735239+00:00
-- url     : https://prove2.me/theorems/aef1917b-b4cd-425f-bedd-f16fe4dc528b
-- title:
--   Proposition 13 — Algorithm 9 ($\rho=r$) is a $(\phi,\lambda)$-ball optimization oracle for $\hat f_\rho$ with $O(L^p/(\lambda\phi^{p-1}))$ queries (one round), depth and work
-- statement:
--   Let $f,g$ satisfy Problem 1. When $\rho=r$, Algorithm 9 is a $(\phi,\lambda)$-ball optimization oracle for $\hat f_\rho$: its output $x$ satisfies
--   $$\mathbb E\Big[\hat f_\rho(x)+\frac\lambda p\|x-\bar x\|_p^p\Big]\le\hat f_\rho(x^\star)+\frac\lambda p\|x^\star-\bar x\|_p^p+\phi,$$
--   with $x^\star$ the minimizer over $B_p(\bar x,r)$. It makes $O(L^p/(\lambda\phi^{p-1}))$ total queries to $g$ with constant query depth, and an additional computational cost of $O(L^p/(\lambda\phi^{p-1}))$ depth and work.
--
--   In the Lean statement, for each admissible $C_p$ there is one constant $C$ such that, for every instance, the guarantee above holds, $2T\le C\,L^p/(\lambda\phi^{p-1})$, and the number of proximal updates is at most $C\,L^p/(\lambda\phi^{p-1})$.
--
--   This is the ball-oracle implementation that Theorem 14 plugs into ball acceleration: all of its queries go in one parallel round.
--
--   **Formalization Note.** Algorithm 9 is defined with its $2T$ queries in one round (line 4), so "constant query depth" holds by construction and is not restated. The source's printed query bound fails for large $\phi$, since $2T\ge2$ always; it is stated as printed (INSIGHTS I2).
--
--   Differences from the source:
--   - encoding: a stochastic gradient oracle g with E[g(x)] ∈ ∂f(x) and E‖g(x)‖_q^q ≤ L^q (Problem 1) → a jointly measurable map g(x, u) of the query point and one uniform draw u ∈ [0, 1] (`IsGradOracle`); each query uses a fresh draw; reason: every Markov kernel into ℝ^d is the law of such a map, so the class of oracles is the same; measurability in x is the field's standing convention, needed for expectations over random query points
--   - encoding: ξ_i ∼ GG_p(0, ρ²I_d), i ∈ [2T], sampled independently, and g(x̄ + ξ_i) queried with independent oracle randomness (lines 3–4) → an i.i.d. sequence (ξ_i, U_i)_{i ≥ 1} with law GG_p(0, r²) ⊗ Unif[0, 1] (`IsAlg9SampleLaw`), answer i being g(x̄ + ξ_i, U_i); ρ = r; reason: the epochs the loop executes use only indices i ≤ T ≤ 2T, so the extra samples are never read; Algorithm 9's input requires r = ρ
--   - reading: (ϕ, λ)-ball optimization oracle for f̂_ρ (Definition 7, x⋆_{x̄,λ} undefined on the page) → BallOracleGuarantee with x⋆ any minimizer of f̂_ρ + (λ/p)‖· − x̄‖_p^p over B_p(x̄, r); reason: Propositions 11–12 say to interpret local minimization over X ∩ B_p(x̄, r), here X = ℝ^d
--   - reading: O(L^p/(λϕ^{p−1})) with Algorithm 9's C_p → for every C_p ≥ the printed bound there is C > 0 (depending on p and C_p only) bounding every instance; reason: O(·) as an explicit constant fixed before the instance; C_p is the algorithm's own parameter
--   - reading: an additional computational cost of O(L^p/(λϕ^{p−1})) depth and work → the number of Bregman proximal updates (alg9Updates) and the number 2T of samples/queries are both ≤ C L^p/(λϕ^{p−1}); reason: the proof counts depth and work as at most T proximal updates and O(T) vector operations, each of constant depth and work; every pass of the algorithm does O(1) vector operations per sample or update
-- source:
--   Nie, Shyam, Bullins, Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in ℓp Geometries, STOC 2027 submission (manuscript, sha256 fe68639b…), p. 63, Proposition 13

import Mathlib
import Definitions.Def_ParallelLpSCO_EpochDA_Basics
import Definitions.Def_ParallelLpSCO_EpochDA_Algorithms

open MeasureTheory

namespace ParallelLpSCO.EpochDA

/-- Proposition 13 (p. 63). For every admissible `C_p` there is a constant `C` such that, under
Problem 1 and with `ρ = r`, Algorithm 9 is a `(ϕ, λ)`-ball optimization oracle for `f̂_ρ` (local
minimization over `B_p(x̄, r)`), its `2T` queries (one parallel round) are at most
`C L^p / (λ ϕ^{p−1})`, and so are its Bregman proximal updates. -/
theorem proposition_13 (p : ℝ) (hp : 2 ≤ p) (Cp : ℝ) (hCp : alg9CpMin p ≤ Cp) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (f : Vec d → ℝ), ConvexOn ℝ Set.univ f → ∀ (L : ℝ), 0 < L →
      ∀ (g : Oracle d), Measurable (Function.uncurry g) → IsGradOracle p L f g →
      ∀ (xbar : Vec d) (r lam phi : ℝ), 0 < r → 0 < lam → 0 < phi →
      ∀ xstar : Vec d, IsBallProx p (fHat p r f) Set.univ r lam xbar xstar →
        (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (ξ : ℕ → Ω → Vec d) (U : ℕ → Ω → unitInterval), IsAlg9SampleLaw p r P ξ U →
          BallOracleGuarantee p (fHat p r f) lam phi xbar xstar P fun ω =>
            alg9Output p r lam phi L Cp xbar (fun i => ξ i ω)
              (fun i => g (xbar + ξ i ω) (U i ω))) ∧
        (alg9Queries p L lam phi Cp : ℝ) ≤ C * (L ^ p / (lam * phi ^ (p - 1))) ∧
        (alg9Updates p L lam phi Cp : ℝ) ≤ C * (L ^ p / (lam * phi ^ (p - 1))) := by sorry

end ParallelLpSCO.EpochDA
