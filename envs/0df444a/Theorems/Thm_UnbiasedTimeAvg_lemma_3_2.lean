-- Prove2me | Theorems.Thm_UnbiasedTimeAvg_lemma_3_2
-- name    : UnbiasedTimeAvg.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:22:32.409437+00:00
-- url     : https://prove2.me/theorems/095921c1-db98-46bd-bc93-21ff8d5b24c4
-- title:
--   Lemma 3.2 — cost and second moment of $Z_k$; unbiasedness when (3.4) is finite
-- statement:
--   Assume the standing model and Assumption A1 with rate $\nu$, $k\ge1$, $b'(k)\le k/2$, and let $\mu=\lim_h\mathbb E f(X_h)$. Let $(p_l)$ be any probability distribution on $\mathbb N$ with $p_l>0$ for all $l$, and $N$ independent of $(U_i)_{i\in\mathbb Z}$ with $\Pr(N=l)=p_l$. Then $T_k\le3k\sum_{l\ge0}2^lp_l$, and
--   $$k\,\mathbb E(Z_k^2)\le2\big(\bar\nu(\lfloor b'(k)/2\rfloor)\big)^2\Big(\frac1{p_0}+\frac1{p_1}\Big)+\sum_{l=2}^\infty\frac{2^{3-l}\big(\bar\nu(k2^{l-2})-\bar\nu(k2^{l-1})\big)^2}{p_l}.\qquad(3.4)$$
--   If the right-hand side of (3.4) is finite, then $Z_k$ is square-integrable and $\mathbb E(f_{k,0}+Z_k)=\mu$.
--
--   This reduces the analysis of $Z_k$ to the choice of $(p_l)$.
--
--   Differences from the source:
--   - reading: ν a "positive decreasing sequence" (A1, p.4) → `0 < ν i` and `Antitone ν` (non-increasing); reason: "decreasing" is ambiguous between strict and non-strict; the non-strict reading is the weaker hypothesis and covers the strict one, and every step of the proof uses only ν(i) ≥ ν(j) for i ≤ j
--   - encoding: (2.5) E((f(X_{i,m}) − f(X_i))²) ≤ ν(i) → lower Lebesgue integral of the square compared with ν(i) in [0, ∞]; reason: the same expectation whether or not the square is integrable; changes no instance
--   - encoding: X_{i,m} = G_{i+m}(X_0; U_{−m}, …, U_{i−1}) with i.i.d. U_i, i ∈ ℤ → `coupledChain g x₀ U i m` (the chain started from x₀ at integer time −m) inside the structure `ChainModel`; reason: the same random variables; `ChainModel` collects the standing assumptions of pp.2 and 4 (measurable g and f, i.i.d. noise on ℤ, f(X_i) square-integrable)
--   - encoding: burn-in b′(k) ≤ k/2 (§3.2, p.8) → a natural `b'` with `2 * b' ≤ k`; reason: the statement is for one fixed k; b(k) does not enter it
--   - encoding: µ, the limit of E(f(X_h)) (Theorem 2.1) → a real µ with the hypothesis `Tendsto (fun h => E f(X_h)) atTop (𝓝 µ)`; reason: Theorem 2.1 (milestone) proves the limit exists, so the hypothesis only names it
--   - encoding: N independent of (U_i, i ∈ ℤ) with Pr(N = l) = p_l → `Measurable N`, `IndepFun N (fun ω i => U i ω) P` (product σ-algebra on ℤ → F′), `P {N = l} = ofReal (p l)`; reason: independence from the whole sequence, as on p.8
--   - encoding: (p_l, l ≥ 0) a probability distribution with p_l > 0, and Pr(N = l) = p_l → `∀ l, 0 < p l` and `P {N = l} = ofReal (p l)`, with no separate hypothesis `Σ p_l = 1`; reason: the law of N already forces Σ p_l = Σ Pr(N = l) = 1, so a separate hypothesis would be redundant; same instances
--   - encoding: T_k, the expected time to simulate Z_k, under "the expected time to simulate f_{k,l} is equal to k2^l" (p.8) → `costZ p k = Σ_l p_l · 3k2^l`; reason: the paper's stated cost model (simulating Z_k at level l computes f_{k,l+1} and f_{k,l}, p.28), taken as the definition; it is not a theorem about running time
--   - encoding: (3.4) with a possibly infinite right-hand side → both sides in [0, ∞]: the lower integral of Z_k² and an `ENNReal` sum, the sum over l ≥ 2 reindexed by l = j + 2; reason: the paper notes that (3.4) holds trivially when the right side is infinite (p.28); same instances
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), Lemma 3.2, (3.4), p.8; proof Appendix F, pp.27–28

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_ChainModel
import Definitions.Def_UnbiasedTimeAvg_AssumptionA1
import Definitions.Def_UnbiasedTimeAvg_nuBar
import Definitions.Def_UnbiasedTimeAvg_levelEstimator
import Definitions.Def_UnbiasedTimeAvg_singleTermEstimator
import Definitions.Def_UnbiasedTimeAvg_costZ

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace UnbiasedTimeAvg

/-- **Lemma 3.2 (cost, second moment and unbiasedness of `Z_k` for any level law).** Kahalé,
arXiv:2209.09581v1, Lemma 3.2, p.8: "For `k ≥ 1`, we have `T_k ≤ 3k Σ_{l=0}^∞ 2^l p_l`, and
`kE(Z_k²) ≤ 2(ν̄(⌊b′(k)/2⌋))²(1/p_0 + 1/p_1) + Σ_{l=2}^∞ 2^{3−l}(ν̄(k2^{l−2}) − ν̄(k2^{l−1}))²/p_l`
(3.4). If the right-hand side of (3.4) is finite, then `Z_k` is square-integrable and
`E(f_{k,0} + Z_k) = µ`."

Setting of Step 2, p.8: `(p_l)` is any probability distribution on `ℕ` with `p_l > 0`, and `N` is
independent of `(U_i, i ∈ ℤ)` with `Pr(N = l) = p_l`; A1 holds, `k ≥ 1`, `b′(k) ≤ k/2`; `µ` is the
limit of `E(f(X_h))` (Theorem 2.1).

**Formalization Note.** (3.4) is stated in `[0, ∞]` (the paper: "If the right-hand side of (3.4)
is infinite, then (3.4) clearly holds", p.28), with the sum over `l ≥ 2` reindexed by `l = j + 2`
(`2^{3−l} = 2^{1−j}`). `T_k` is `costZ p k`, the paper's cost model, so its bound is an identity
of the definitions. `µ` enters through the hypothesis that it is the limit. That `(p_l)` sums to `1`
is implied by `Pr(N = l) = p_l` for all `l`, so it is not a separate hypothesis. -/
theorem lemma_3_2
    {Ω F F' : Type*} [MeasurableSpace Ω] [MeasurableSpace F] [MeasurableSpace F']
    {P : Measure Ω} [IsProbabilityMeasure P] {U : ℤ → Ω → F'} {g : F → F' → F} {f : F → ℝ}
    {x₀ : F} (hM : ChainModel P U g f x₀) {ν : ℕ → ℝ} (hA1 : AssumptionA1 P U g f x₀ ν)
    (b' k : ℕ) (hk : 1 ≤ k) (hb' : 2 * b' ≤ k)
    (p : ℕ → ℝ) (hp_pos : ∀ l, 0 < p l)
    (N : Ω → ℕ) (hN : Measurable N) (hN_indep : IndepFun N (fun ω i => U i ω) P)
    (hN_law : ∀ l, P {ω | N ω = l} = ENNReal.ofReal (p l))
    (μ : ℝ) (hμ : Tendsto (fun h : ℕ => ∫ ω, f (coupledChain g x₀ U h 0 ω) ∂P) atTop (𝓝 μ)) :
    let M : ℝ≥0∞ := ENNReal.ofReal (2 * (nuBar ν (b' / 2)) ^ 2 * (1 / p 0 + 1 / p 1)) +
      ∑' j : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((1 : ℤ) - j) *
        (nuBar ν (k * 2 ^ j) - nuBar ν (k * 2 ^ (j + 1))) ^ 2 / p (j + 2))
    costZ p k ≤ 3 * k * ∑' l : ℕ, 2 ^ l * p l ∧
    (k : ℝ≥0∞) * ∫⁻ ω, ENNReal.ofReal ((singleTermEstimator g x₀ U f b' k p N ω) ^ 2) ∂P ≤ M ∧
    (M ≠ ⊤ → MemLp (singleTermEstimator g x₀ U f b' k p N) 2 P ∧
      ∫ ω, (levelEstimator g x₀ U f b' k 0 ω + singleTermEstimator g x₀ U f b' k p N ω) ∂P = μ) := by sorry

end UnbiasedTimeAvg
