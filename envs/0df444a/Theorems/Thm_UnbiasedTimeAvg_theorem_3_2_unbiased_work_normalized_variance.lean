-- Prove2me | Theorems.Thm_UnbiasedTimeAvg_theorem_3_2_unbiased_work_normalized_variance
-- name    : UnbiasedTimeAvg.theorem_3_2_unbiased_work_normalized_variance
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:22:48.89907+00:00
-- url     : https://prove2.me/theorems/0eeae81f-572f-4118-b554-6b0ceb70e099
-- title:
--   Theorem 3.2 — $\hat f_k$ is square-integrable and unbiased, $\hat T_k\le k+9qk$, and $\hat T_k\mathrm{Var}(\hat f_k)\le k\mathrm{Var}(f_k)+8610\bar\nu(0)^2\max(q,\sqrt{(b'(k)-b(k))/k})$
-- statement:
--   Let $X_0=x_0$ be deterministic and $X_{i+1}=g(X_i,U_i)$ with $(U_i)_{i\in\mathbb Z}$ i.i.d., $f$ measurable with $f(X_i)$ square-integrable, and assume A1 with rate $\nu$. Let $\mu=\lim_h\mathbb E f(X_h)$, $k\ge1$ and $b(k)\le b'(k)\le k/2$. Let $(p_l)$ be given by (3.6)–(3.7) and $q=\bar\nu(\lfloor b'(k)/2\rfloor)/\bar\nu(0)$ by (3.10). Let $N$ be independent of $(U_i)_{i\in\mathbb Z}$ with $\Pr(N=l)=p_l$, $Z_k=(f_{k,N+1}-f_{k,N})/p_N$, $Z'_k$ a copy of $Z_k$ independent of $f_{k,0}$, $Q$ a binary variable independent of $(f_{k,0},Z'_k)$ with $\Pr(Q=1)=q$, and
--   $$\hat f_k=f_{k,0}+q^{-1}QZ'_k.$$
--   With $T_k=\sum_lp_l\,3k2^l$ and $\hat T_k=k+qT_k$ the expected costs of $Z_k$ and $\hat f_k$:
--
--   1. $\hat f_k$ is square-integrable and $\mathbb E(\hat f_k)=\mu$;
--   2. $\hat T_k\le k+9qk$;
--   3. $$\hat T_k\,\mathrm{Var}(\hat f_k)\le k\,\mathrm{Var}(f_k)+8610\,\bar\nu(0)^2\max\Big(q,\sqrt{\frac{b'(k)-b(k)}{k}}\Big).\qquad(3.11)$$
--
--   The estimator $\hat f_k$ is an unbiased estimator of the steady-state mean $\mu$ built from finitely many simulation steps, and (3.11) compares its work-normalized variance with that of the conventional time average $f_k$: when the second term is $o(1)$ and $k\,\mathrm{Var}(f_k)$ stays bounded below, $\hat f_k$ is asymptotically at least as efficient as $f_k$.
--
--   **Formalization Note** $T_k$ and $\hat T_k$ are the paper's cost model (expected time $k2^l$ for $f_{k,l}$), not a machine model; the conclusion also states that the series defining $T_k$ converges.
--
--   Differences from the source:
--   - reading: ν a "positive decreasing sequence" (A1, p.4) → `0 < ν i` and `Antitone ν` (non-increasing); reason: "decreasing" is ambiguous between strict and non-strict; the non-strict reading is the weaker hypothesis and covers the strict one, and every step of the proof uses only ν(i) ≥ ν(j) for i ≤ j
--   - encoding: (2.5) E((f(X_{i,m}) − f(X_i))²) ≤ ν(i) → lower Lebesgue integral of the square compared with ν(i) in [0, ∞]; reason: the same expectation whether or not the square is integrable; changes no instance
--   - encoding: X_{i,m} = G_{i+m}(X_0; U_{−m}, …, U_{i−1}) with i.i.d. U_i, i ∈ ℤ → `coupledChain g x₀ U i m` (the chain started from x₀ at integer time −m) inside the structure `ChainModel`; reason: the same random variables; `ChainModel` collects the standing assumptions of pp.2 and 4 (measurable g and f, i.i.d. noise on ℤ, f(X_i) square-integrable)
--   - encoding: burn-ins b(k), b′(k) with b(k) ≤ b′(k) ≤ k/2 → two naturals `b ≤ b'` with `2 * b' ≤ k`; reason: the theorem is for one fixed k, so b(k) and b′(k) are two numbers; 2b′ ≤ k is b′ ≤ k/2
--   - encoding: µ, the limit of E(f(X_h)) (Theorem 2.1) → a real µ with the hypothesis `Tendsto (fun h => E f(X_h)) atTop (𝓝 µ)`; reason: Theorem 2.1 (milestone) proves the limit exists, so the hypothesis only names it
--   - encoding: N independent of (U_i, i ∈ ℤ) with Pr(N = l) = p_l → `Measurable N`, `IndepFun N (fun ω i => U i ω) P` (product σ-algebra on ℤ → F′), `P {N = l} = ofReal (p l)`; reason: independence from the whole sequence, as on p.8
--   - encoding: T_k, the expected time to simulate Z_k, under "the expected time to simulate f_{k,l} is equal to k2^l" (p.8) → `costZ p k = Σ_l p_l · 3k2^l`; reason: the paper's stated cost model (simulating Z_k at level l computes f_{k,l+1} and f_{k,l}, p.28), taken as the definition; it is not a theorem about running time
--   - encoding: T̂_k, the expected time to simulate f̂_k → `costFhat p q k = k + q · costZ p k`; reason: the paper's identity T̂_k = k + qT_k (p.9) under its cost model, taken as the definition
--   - encoding: T̂_k ≤ k + 9qk → summability of l ↦ p_l·3k2^l together with the inequality; reason: a real `tsum` of a divergent series is 0 in Lean; the paper's T_k is a finite expectation
--   - encoding: Z′_k a copy of Z_k independent of f_{k,0}; Q binary, independent of (f_{k,0}, Z′_k), Pr(Q = 1) = q → `IdentDistrib Z' Z_k`, `IndepFun f_{k,0} Z'`, `Measurable Q`, `Q ω ∈ {0,1}`, `P {Q = 1} = ofReal q`, `IndepFun Q (f_{k,0}, Z')`, all on the probability space of the noise; reason: the paper's words on p.9, one space carrying all variables
--   - encoding: Var(·) → `ProbabilityTheory.variance`; reason: the conclusion states square-integrability of f̂_k, and f_k is square-integrable by the standing model, so both variances are true variances
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), Theorem 3.2, (3.11), p.10; construction §3.2–3.3, pp.8–9; proof Appendix I, p.30

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_ChainModel
import Definitions.Def_UnbiasedTimeAvg_AssumptionA1
import Definitions.Def_UnbiasedTimeAvg_nuBar
import Definitions.Def_UnbiasedTimeAvg_timeAvgEstimator
import Definitions.Def_UnbiasedTimeAvg_levelEstimator
import Definitions.Def_UnbiasedTimeAvg_singleTermEstimator
import Definitions.Def_UnbiasedTimeAvg_debiasedEstimator
import Definitions.Def_UnbiasedTimeAvg_levelProb
import Definitions.Def_UnbiasedTimeAvg_coinProb
import Definitions.Def_UnbiasedTimeAvg_costFhat

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace UnbiasedTimeAvg

/-- **Theorem 3.2 (the unbiased estimator `f̂_k`).** Kahalé, arXiv:2209.09581v1, Theorem 3.2,
p.10: "Suppose that A1 holds, that `k ≥ 1`, and that `(p_l, l ≥ 0)` and `q` are given by (3.6),
(3.7) and (3.10). Then `f̂_k` is square-integrable and `E(f̂_k) = µ`. Moreover, `T̂_k ≤ k + 9qk`,
and `T̂_k Var(f̂_k) ≤ k Var(f_k) + 8610(ν̄(0))² max(q, √((b′(k) − b(k))/k))` (3.11)."

The construction (pp.8–9): `b(k) ≤ b′(k) ≤ k/2`; `N` is independent of `(U_i, i ∈ ℤ)` with
`Pr(N = l) = p_l`, and `Z_k = (f_{k,N+1} − f_{k,N})/p_N` (3.3); `Z′_k` is a copy of `Z_k` independent
of `f_{k,0}`; `Q` is a binary variable independent of `(f_{k,0}, Z′_k)` with `Pr(Q = 1) = q`; and
`f̂_k = f_{k,0} + q⁻¹QZ′_k` (3.5). `T̂_k = k + qT_k` is the expected time to simulate `f̂_k` and
`µ = lim_h E(f(X_h))` (Theorem 2.1).

**Formalization Note.** `T_k`, `T̂_k` are the paper's cost model (`costZ`, `costFhat`); the
conclusion also states that the series defining `T_k` converges. `µ` enters as the hypothesis that
it is the limit of `E(f(X_h))`. `b`, `b'` are `b(k)`, `b′(k)` at the fixed `k`. -/
theorem theorem_3_2_unbiased_work_normalized_variance
    {Ω F F' : Type*} [MeasurableSpace Ω] [MeasurableSpace F] [MeasurableSpace F']
    {P : Measure Ω} [IsProbabilityMeasure P] {U : ℤ → Ω → F'} {g : F → F' → F} {f : F → ℝ}
    {x₀ : F} (hM : ChainModel P U g f x₀) {ν : ℕ → ℝ} (hA1 : AssumptionA1 P U g f x₀ ν)
    (b b' k : ℕ) (hk : 1 ≤ k) (hbb' : b ≤ b') (hb' : 2 * b' ≤ k)
    (μ : ℝ) (hμ : Tendsto (fun h : ℕ => ∫ ω, f (coupledChain g x₀ U h 0 ω) ∂P) atTop (𝓝 μ))
    (N : Ω → ℕ) (hN : Measurable N) (hN_indep : IndepFun N (fun ω i => U i ω) P)
    (hN_law : ∀ l, P {ω | N ω = l} = ENNReal.ofReal (levelProb ν k l))
    (Z' : Ω → ℝ)
    (hZ'_copy : IdentDistrib Z' (singleTermEstimator g x₀ U f b' k (levelProb ν k) N) P P)
    (hZ'_indep : IndepFun (levelEstimator g x₀ U f b' k 0) Z' P)
    (Q : Ω → ℝ) (hQ_meas : Measurable Q) (hQ_bin : ∀ ω, Q ω = 0 ∨ Q ω = 1)
    (hQ_law : P {ω | Q ω = 1} = ENNReal.ofReal (coinProb ν b'))
    (hQ_indep : IndepFun Q (fun ω => (levelEstimator g x₀ U f b' k 0 ω, Z' ω)) P) :
    MemLp (debiasedEstimator g x₀ U f b' k (coinProb ν b') Q Z') 2 P ∧
    ∫ ω, debiasedEstimator g x₀ U f b' k (coinProb ν b') Q Z' ω ∂P = μ ∧
    Summable (fun l : ℕ => levelProb ν k l * (3 * (k : ℝ) * 2 ^ l)) ∧
    costFhat (levelProb ν k) (coinProb ν b') k ≤ k + 9 * coinProb ν b' * k ∧
    costFhat (levelProb ν k) (coinProb ν b') k *
        variance (debiasedEstimator g x₀ U f b' k (coinProb ν b') Q Z') P
      ≤ k * variance (timeAvgEstimator g x₀ U f b k) P
        + 8610 * (nuBar ν 0) ^ 2 * max (coinProb ν b') (Real.sqrt (((b' : ℝ) - b) / k)) := by sorry

end UnbiasedTimeAvg
