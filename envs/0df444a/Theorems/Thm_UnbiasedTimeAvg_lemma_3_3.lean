-- Prove2me | Theorems.Thm_UnbiasedTimeAvg_lemma_3_3
-- name    : UnbiasedTimeAvg.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:22:27.955326+00:00
-- url     : https://prove2.me/theorems/8f695a27-04ce-4dfd-aafd-4598e59c4b61
-- title:
--   Lemma 3.3 — with (3.6)–(3.7): $\mathbb E(f_{k,0}+Z_k)=\mu$, $T_k\le9k$, $k\mathbb E(Z_k^2)\le20\bar\nu(\lfloor b'(k)/2\rfloor)^2$
-- statement:
--   Assume the standing model and Assumption A1 with rate $\nu$, $k\ge1$, $b'(k)\le k/2$, $\mu=\lim_h\mathbb E f(X_h)$, and let $(p_l)$ be given by (3.6)–(3.7), with $N$ independent of $(U_i)_{i\in\mathbb Z}$ and $\Pr(N=l)=p_l$. Then $Z_k$ is square-integrable,
--   $$\mathbb E(f_{k,0}+Z_k)=\mu,\qquad T_k\le9k,\qquad k\,\mathbb E(Z_k^2)\le20\big(\bar\nu(\lfloor b'(k)/2\rfloor)\big)^2.\qquad(3.9)$$
--
--   With these parameters the correction $Z_k$ is unbiased for $\mu-\mathbb E f_{k,0}$, costs $O(k)$, and has second moment of the order of the squared bias bound.
--
--   Differences from the source:
--   - reading: ν a "positive decreasing sequence" (A1, p.4) → `0 < ν i` and `Antitone ν` (non-increasing); reason: "decreasing" is ambiguous between strict and non-strict; the non-strict reading is the weaker hypothesis and covers the strict one, and every step of the proof uses only ν(i) ≥ ν(j) for i ≤ j
--   - encoding: (2.5) E((f(X_{i,m}) − f(X_i))²) ≤ ν(i) → lower Lebesgue integral of the square compared with ν(i) in [0, ∞]; reason: the same expectation whether or not the square is integrable; changes no instance
--   - encoding: X_{i,m} = G_{i+m}(X_0; U_{−m}, …, U_{i−1}) with i.i.d. U_i, i ∈ ℤ → `coupledChain g x₀ U i m` (the chain started from x₀ at integer time −m) inside the structure `ChainModel`; reason: the same random variables; `ChainModel` collects the standing assumptions of pp.2 and 4 (measurable g and f, i.i.d. noise on ℤ, f(X_i) square-integrable)
--   - encoding: burn-in b′(k) ≤ k/2 (§3.2, p.8) → a natural `b'` with `2 * b' ≤ k`; reason: the statement is for one fixed k; b(k) does not enter it
--   - encoding: µ, the limit of E(f(X_h)) (Theorem 2.1) → a real µ with the hypothesis `Tendsto (fun h => E f(X_h)) atTop (𝓝 µ)`; reason: Theorem 2.1 (milestone) proves the limit exists, so the hypothesis only names it
--   - encoding: N independent of (U_i, i ∈ ℤ) with Pr(N = l) = p_l → `Measurable N`, `IndepFun N (fun ω i => U i ω) P` (product σ-algebra on ℤ → F′), `P {N = l} = ofReal (p l)`; reason: independence from the whole sequence, as on p.8
--   - encoding: T_k, the expected time to simulate Z_k, under "the expected time to simulate f_{k,l} is equal to k2^l" (p.8) → `costZ p k = Σ_l p_l · 3k2^l`; reason: the paper's stated cost model (simulating Z_k at level l computes f_{k,l+1} and f_{k,l}, p.28), taken as the definition; it is not a theorem about running time
--   - encoding: E(Z_k²) in (3.9) → the conclusion also states `MemLp Z_k 2` and uses the Bochner integral of Z_k²; reason: (3.9) asserts that E(Z_k²) is finite, i.e. that Z_k is square-integrable (Lemma 3.2); stating it makes the integral the true second moment
--   - encoding: T_k ≤ 9k → summability of l ↦ p_l·3k2^l together with `costZ p k ≤ 9k`; reason: a real `tsum` of a divergent series is 0 in Lean; the paper's T_k is a finite expectation
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), Lemma 3.3, (3.9), p.9; proof Appendix G, p.29

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_ChainModel
import Definitions.Def_UnbiasedTimeAvg_AssumptionA1
import Definitions.Def_UnbiasedTimeAvg_nuBar
import Definitions.Def_UnbiasedTimeAvg_levelEstimator
import Definitions.Def_UnbiasedTimeAvg_singleTermEstimator
import Definitions.Def_UnbiasedTimeAvg_levelProb
import Definitions.Def_UnbiasedTimeAvg_costZ

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace UnbiasedTimeAvg

/-- **Lemma 3.3 (`Z_k` with the `ν̄`-dependent levels).** Kahalé, arXiv:2209.09581v1,
Lemma 3.3, p.9: "Suppose that A1 holds and that `(p_l, l ≥ 0)` are given by (3.6) and (3.7). For
`k ≥ 1`, we have `E(f_{k,0} + Z_k) = µ`, `T_k ≤ 9k`, and `kE(Z_k²) ≤ 20(ν̄(⌊b′(k)/2⌋))²` (3.9)."

`N` is independent of `(U_i, i ∈ ℤ)` with `Pr(N = l) = p_l` ((3.3), p.8), `b′(k) ≤ k/2`, and `µ` is
the limit of `E(f(X_h))`.

**Formalization Note.** The conclusion also records that `Z_k` is square-integrable (so `E(Z_k²)`
is a true second moment; Lemma 3.2 gives it) and that the series defining `T_k = costZ p k`
converges (a real `tsum` of a divergent series would be `0`). -/
theorem lemma_3_3
    {Ω F F' : Type*} [MeasurableSpace Ω] [MeasurableSpace F] [MeasurableSpace F']
    {P : Measure Ω} [IsProbabilityMeasure P] {U : ℤ → Ω → F'} {g : F → F' → F} {f : F → ℝ}
    {x₀ : F} (hM : ChainModel P U g f x₀) {ν : ℕ → ℝ} (hA1 : AssumptionA1 P U g f x₀ ν)
    (b' k : ℕ) (hk : 1 ≤ k) (hb' : 2 * b' ≤ k)
    (N : Ω → ℕ) (hN : Measurable N) (hN_indep : IndepFun N (fun ω i => U i ω) P)
    (hN_law : ∀ l, P {ω | N ω = l} = ENNReal.ofReal (levelProb ν k l))
    (μ : ℝ) (hμ : Tendsto (fun h : ℕ => ∫ ω, f (coupledChain g x₀ U h 0 ω) ∂P) atTop (𝓝 μ)) :
    MemLp (singleTermEstimator g x₀ U f b' k (levelProb ν k) N) 2 P ∧
    ∫ ω, (levelEstimator g x₀ U f b' k 0 ω +
      singleTermEstimator g x₀ U f b' k (levelProb ν k) N ω) ∂P = μ ∧
    Summable (fun l : ℕ => levelProb ν k l * (3 * (k : ℝ) * 2 ^ l)) ∧
    costZ (levelProb ν k) k ≤ 9 * k ∧
    (k : ℝ) * ∫ ω, (singleTermEstimator g x₀ U f b' k (levelProb ν k) N ω) ^ 2 ∂P
      ≤ 20 * (nuBar ν (b' / 2)) ^ 2 := by sorry

end UnbiasedTimeAvg
