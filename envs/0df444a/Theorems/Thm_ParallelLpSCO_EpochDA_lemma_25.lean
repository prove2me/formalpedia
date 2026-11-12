-- Prove2me | Theorems.Thm_ParallelLpSCO_EpochDA_lemma_25
-- name    : ParallelLpSCO.EpochDA.lemma_25
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:06:19.375791+00:00
-- url     : https://prove2.me/theorems/35ed0f11-3938-4272-95b7-2241c97d30f2
-- title:
--   Lemma 25 — after epoch $k$ of Algorithm 9 the expected regularized gap is at most $(4L)^q/(\lambda^{q-1}2^k)$
-- statement:
--   In the setting of Lemma 24 (Problem 1 with $L>0$; Algorithm 9 with $r=\rho$, $\lambda,\phi>0$, admissible $C_p$; $x^\star$ the minimizer of $\hat f_\rho+\frac\lambda p\|\cdot-\bar x\|_p^p$ over $B_p(\bar x,r)$), after each completed epoch $k$,
--   $$\mathbb E\Big[\hat f_\rho(x^0_{k+1})+\frac\lambda p\|x^0_{k+1}-\bar x\|_p^p\Big]-\hat f_\rho(x^\star)-\frac\lambda p\|x^\star-\bar x\|_p^p\le\frac{(4L)^q}{\lambda^{q-1}2^k}.\qquad(53)$$
--
--   The gap halves with every epoch while epoch lengths grow by $2^{p-1}$. Proposition 13 converts this into the query count of one ball-oracle call.
--
--   Differences from the source:
--   - encoding: a stochastic gradient oracle g with E[g(x)] ∈ ∂f(x) and E‖g(x)‖_q^q ≤ L^q (Problem 1) → a jointly measurable map g(x, u) of the query point and one uniform draw u ∈ [0, 1] (`IsGradOracle`); each query uses a fresh draw; reason: every Markov kernel into ℝ^d is the law of such a map, so the class of oracles is the same; measurability in x is the field's standing convention, needed for expectations over random query points
--   - reading: x⋆ = argmin_{x ∈ B_p(x̄, r)} {f̂_ρ(x) + (λ/p)‖x − x̄‖_p^p} → any minimizer x⋆ of that objective over B_p(x̄, r) (`IsBallProx` with X = ℝ^d); reason: the objective is strictly convex and continuous on a compact ball, so the minimizer exists and is unique; only its value and location are used
--   - encoding: ξ_i ∼ GG_p(0, ρ²I_d), i ∈ [2T], sampled independently, and g(x̄ + ξ_i) queried with independent oracle randomness (lines 3–4) → an i.i.d. sequence (ξ_i, U_i)_{i ≥ 1} with law GG_p(0, r²) ⊗ Unif[0, 1] (`IsAlg9SampleLaw`), answer i being g(x̄ + ξ_i, U_i); ρ = r; reason: the epochs the loop executes use only indices i ≤ T ≤ 2T, so the extra samples are never read; Algorithm 9's input requires r = ρ
--   - reading: each (completed) epoch k of Algorithm 9 → each k ≥ 1 with T_1 + … + T_k ≤ T (the epochs the while-loop of lines 6–14 executes); reason: this is exactly the set of epochs Algorithm 9 runs
--   - encoding: E[f̂_ρ(x^0_{k+1}) + (λ/p)‖x^0_{k+1} − x̄‖_p^p] → the same Bochner integral, together with the integrability of the random variable; reason: the source takes the expectation to exist; Lean's integral of a non-integrable function is 0, so existence is stated
-- source:
--   Nie, Shyam, Bullins, Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in ℓp Geometries, STOC 2027 submission (manuscript, sha256 fe68639b…), p. 63, Lemma 25

import Mathlib
import Definitions.Def_ParallelLpSCO_EpochDA_Basics
import Definitions.Def_ParallelLpSCO_EpochDA_Algorithms

open MeasureTheory

namespace ParallelLpSCO.EpochDA

/-- Lemma 25 (p. 63). In the setting of Lemma 24, after each completed epoch `k` of
Algorithm 9,
`E[f̂_ρ(x^0_{k+1}) + (λ/p)‖x^0_{k+1} − x̄‖_p^p] − f̂_ρ(x⋆) − (λ/p)‖x⋆ − x̄‖_p^p ≤ (4L)^q / (λ^{q−1} 2^k)`. -/
theorem lemma_25 (p : ℝ) (hp : 2 ≤ p) (d : ℕ) (f : Vec d → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (L : ℝ) (hL : 0 < L) (g : Oracle d) (hgm : Measurable (Function.uncurry g))
    (hg : IsGradOracle p L f g) (xbar : Vec d) (r lam phi Cp : ℝ) (hr : 0 < r) (hlam : 0 < lam)
    (hphi : 0 < phi) (hCp : alg9CpMin p ≤ Cp) (xstar : Vec d)
    (hxstar : IsBallProx p (fHat p r f) Set.univ r lam xbar xstar)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Vec d) (U : ℕ → Ω → unitInterval) (hlaw : IsAlg9SampleLaw p r P ξ U)
    (k : ℕ) (hk : 1 ≤ k) (hrun : cumLen p k ≤ alg9T p L lam phi Cp) :
    let x0 : ℕ → Ω → Vec d := fun j ω =>
      alg9Start p r lam xbar (fun i => ξ i ω) (fun i => g (xbar + ξ i ω) (U i ω)) j
    let q := conjExp p
    Integrable (fun ω => fHat p r f (x0 (k + 1) ω) + lam / p * lpNorm p (x0 (k + 1) ω - xbar) ^ p)
        P ∧
      (∫ ω, (fHat p r f (x0 (k + 1) ω) + lam / p * lpNorm p (x0 (k + 1) ω - xbar) ^ p) ∂P) -
          fHat p r f xstar - lam / p * lpNorm p (xstar - xbar) ^ p ≤
        (4 * L) ^ q / (lam ^ (q - 1) * (2 : ℝ) ^ k) := by sorry

end ParallelLpSCO.EpochDA
