-- Prove2me | Theorems.Thm_ParallelLpSCO_EpochDA_lemma_24
-- name    : ParallelLpSCO.EpochDA.lemma_24
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:05:59.96983+00:00
-- url     : https://prove2.me/theorems/05691095-8e10-4b5f-ac6a-369165a27b3f
-- title:
--   Lemma 24 — one epoch of Algorithm 9: expected regularized gap at most $\mathbb E\|x^\star-x^0_k\|_p^p/(p\eta_kT_k)+\frac{(4L)^q}q(\eta_k/2^{2-p})^{q-1}$
-- statement:
--   Let $f,g$ satisfy Problem 1 with $L>0$, and run Algorithm 9 with $r=\rho>0$, $\lambda,\phi>0$ and $C_p$ above its printed lower bound. Let $x^\star$ minimize $\hat f_\rho(x)+\frac\lambda p\|x-\bar x\|_p^p$ over $B_p(\bar x,r)$. Every epoch $k$ of Algorithm 9 satisfies
--   $$\mathbb E\Big[\hat f_\rho(x^0_{k+1})+\frac\lambda p\|x^0_{k+1}-\bar x\|_p^p\Big]-\hat f_\rho(x^\star)-\frac\lambda p\|x^\star-\bar x\|_p^p\le\frac{\mathbb E\|x^\star-x^0_k\|_p^p}{p\,\eta_kT_k}+\frac{(4L)^q}q\Big(\frac{\eta_k}{2^{2-p}}\Big)^{q-1}.\qquad(50)$$
--   Here $x^0_k$ is the start of epoch $k$, $T_k$ its length and $\eta_k$ its step size.
--
--   This is the one-epoch progress bound of dual averaging with p-GREG estimates: an initial-distance term and a noise term controlled only by the $q$-th moment of the oracle.
--
--   **Formalization Note.** `alg9Start … k` $=x^0_k$, `epochEta p λ k` $=\eta_k$, `epochLen p k` $=T_k$; the random inputs are the i.i.d. sequence $(\xi_i,U_i)$, and the hypothesis `cumLen p k ≤ alg9T …` says epoch $k$ is executed.
--
--   Differences from the source:
--   - encoding: a stochastic gradient oracle g with E[g(x)] ∈ ∂f(x) and E‖g(x)‖_q^q ≤ L^q (Problem 1) → a jointly measurable map g(x, u) of the query point and one uniform draw u ∈ [0, 1] (`IsGradOracle`); each query uses a fresh draw; reason: every Markov kernel into ℝ^d is the law of such a map, so the class of oracles is the same; measurability in x is the field's standing convention, needed for expectations over random query points
--   - reading: x⋆ = argmin_{x ∈ B_p(x̄, r)} {f̂_ρ(x) + (λ/p)‖x − x̄‖_p^p} → any minimizer x⋆ of that objective over B_p(x̄, r) (`IsBallProx` with X = ℝ^d); reason: the objective is strictly convex and continuous on a compact ball, so the minimizer exists and is unique; only its value and location are used
--   - encoding: ξ_i ∼ GG_p(0, ρ²I_d), i ∈ [2T], sampled independently, and g(x̄ + ξ_i) queried with independent oracle randomness (lines 3–4) → an i.i.d. sequence (ξ_i, U_i)_{i ≥ 1} with law GG_p(0, r²) ⊗ Unif[0, 1] (`IsAlg9SampleLaw`), answer i being g(x̄ + ξ_i, U_i); ρ = r; reason: the epochs the loop executes use only indices i ≤ T ≤ 2T, so the extra samples are never read; Algorithm 9's input requires r = ρ
--   - reading: each (completed) epoch k of Algorithm 9 → each k ≥ 1 with T_1 + … + T_k ≤ T (the epochs the while-loop of lines 6–14 executes); reason: this is exactly the set of epochs Algorithm 9 runs
--   - encoding: E[f̂_ρ(x^0_{k+1}) + (λ/p)‖x^0_{k+1} − x̄‖_p^p] → the same Bochner integral, together with the integrability of the random variable; reason: the source takes the expectation to exist; Lean's integral of a non-integrable function is 0, so existence is stated
-- source:
--   Nie, Shyam, Bullins, Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in ℓp Geometries, STOC 2027 submission (manuscript, sha256 fe68639b…), p. 62, Lemma 24

import Mathlib
import Definitions.Def_ParallelLpSCO_EpochDA_Basics
import Definitions.Def_ParallelLpSCO_EpochDA_Algorithms

open MeasureTheory

namespace ParallelLpSCO.EpochDA

/-- Lemma 24 (p. 62). Under Problem 1, for Algorithm 9 run with `r = ρ`, `λ, ϕ > 0` and `C_p`
above its printed lower bound, every epoch `k` the algorithm executes (`∑_{j ≤ k} T_j ≤ T`)
satisfies
`E[f̂_ρ(x^0_{k+1}) + (λ/p)‖x^0_{k+1} − x̄‖_p^p] − f̂_ρ(x⋆) − (λ/p)‖x⋆ − x̄‖_p^p
  ≤ E‖x⋆ − x^0_k‖_p^p / (p η_k T_k) + ((4L)^q / q) (η_k / 2^{2−p})^{q−1}`,
where `x⋆` minimizes `f̂_ρ + (λ/p)‖· − x̄‖_p^p` over `B_p(x̄, r)`. -/
theorem lemma_24 (p : ℝ) (hp : 2 ≤ p) (d : ℕ) (f : Vec d → ℝ) (hf : ConvexOn ℝ Set.univ f)
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
        (∫ ω, lpNorm p (xstar - x0 k ω) ^ p ∂P) / (p * epochEta p lam k * epochLen p k) +
          (4 * L) ^ q / q * (epochEta p lam k / (2 : ℝ) ^ (2 - p)) ^ (q - 1) := by sorry

end ParallelLpSCO.EpochDA
