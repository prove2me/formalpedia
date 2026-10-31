-- Prove2me | Theorems.Thm_UnbiasedTimeAvg_lemma_F_2
-- name    : UnbiasedTimeAvg.lemma_F_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:22:07.886835+00:00
-- url     : https://prove2.me/theorems/c46da049-3d67-4c4a-8f1b-170fb7016b6f
-- title:
--   Lemma F.2 — $\mathbb E\big((Y_l-Y_{l-1})^2\big)\le\nu_{k,l}$
-- statement:
--   Assume the standing model and Assumption A1 with rate $\nu$, $k\ge1$ and $b'(k)\le k/2$. For $l\ge0$ set $Y_l=f_{k,l+1}-f_{k,0}$ and $Y_{-1}=0$, so that $Y_l-Y_{l-1}=f_{k,l+1}-f_{k,l}$. Then for every $l\ge0$,
--   $$\mathbb E\big[(Y_l-Y_{l-1})^2\big]\le\nu_{k,l}.$$
--
--   The level increments are small in $L^2$ because consecutive levels share their recent noise.
--
--   Differences from the source:
--   - reading: ν a "positive decreasing sequence" (A1, p.4) → `0 < ν i` and `Antitone ν` (non-increasing); reason: "decreasing" is ambiguous between strict and non-strict; the non-strict reading is the weaker hypothesis and covers the strict one, and every step of the proof uses only ν(i) ≥ ν(j) for i ≤ j
--   - encoding: (2.5) E((f(X_{i,m}) − f(X_i))²) ≤ ν(i) → lower Lebesgue integral of the square compared with ν(i) in [0, ∞]; reason: the same expectation whether or not the square is integrable; changes no instance
--   - encoding: X_{i,m} = G_{i+m}(X_0; U_{−m}, …, U_{i−1}) with i.i.d. U_i, i ∈ ℤ → `coupledChain g x₀ U i m` (the chain started from x₀ at integer time −m) inside the structure `ChainModel`; reason: the same random variables; `ChainModel` collects the standing assumptions of pp.2 and 4 (measurable g and f, i.i.d. noise on ℤ, f(X_i) square-integrable)
--   - encoding: burn-in b′(k) ≤ k/2 (§3.2, p.8) → a natural `b'` with `2 * b' ≤ k`; reason: the statement is for one fixed k; b(k) does not enter it
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), Lemma F.2, p.28

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_ChainModel
import Definitions.Def_UnbiasedTimeAvg_AssumptionA1
import Definitions.Def_UnbiasedTimeAvg_nuBar
import Definitions.Def_UnbiasedTimeAvg_levelEstimator
import Definitions.Def_UnbiasedTimeAvg_increment
import Definitions.Def_UnbiasedTimeAvg_nuKL

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace UnbiasedTimeAvg

/-- **Lemma F.2 (second moment of the increments).** Kahalé, arXiv:2209.09581v1, p.28: "For
`l ≥ 0`, set `Y_l = f_{k,l+1} − f_{k,0}`, with `Y_{−1} = 0`. … Lemma F.2. For `l ≥ 0`,
`E((Y_l − Y_{l−1})²) ≤ ν_{k,l}`."

Assumption A1 is in force, `k ≥ 1` and `b′(k) ≤ k/2`.

**Formalization Note.** `Y_l − Y_{l−1}` is `increment Y l` for `Y_l = f_{k,l+1} − f_{k,0}`; the
expectation is a Bochner integral. -/
theorem lemma_F_2
    {Ω F F' : Type*} [MeasurableSpace Ω] [MeasurableSpace F] [MeasurableSpace F']
    {P : Measure Ω} [IsProbabilityMeasure P] {U : ℤ → Ω → F'} {g : F → F' → F} {f : F → ℝ}
    {x₀ : F} (hM : ChainModel P U g f x₀) {ν : ℕ → ℝ} (hA1 : AssumptionA1 P U g f x₀ ν)
    (b' k : ℕ) (hk : 1 ≤ k) (hb' : 2 * b' ≤ k) (l : ℕ) :
    ∫ ω, (increment (fun j ω => levelEstimator g x₀ U f b' k (j + 1) ω -
        levelEstimator g x₀ U f b' k 0 ω) l ω) ^ 2 ∂P ≤ nuKL ν b' k l := by sorry

end UnbiasedTimeAvg
