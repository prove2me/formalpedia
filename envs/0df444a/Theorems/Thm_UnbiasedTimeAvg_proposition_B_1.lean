-- Prove2me | Theorems.Thm_UnbiasedTimeAvg_proposition_B_1
-- name    : UnbiasedTimeAvg.proposition_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:26.067896+00:00
-- url     : https://prove2.me/theorems/83158372-cece-48a1-8adb-e3fb1f26e741
-- title:
--   Proposition B.1 — shift invariance of the coupled chains
-- statement:
--   Assume the standing model: $X_0=x_0$ deterministic, $X_{i+1}=g(X_i,U_i)$ with $(U_i)_{i\in\mathbb Z}$ i.i.d., and $X_{i,m}$ the chain started at time $-m$. For integers $n,m,m'$ with $n\ge -m$ and $n\ge-m'$, the pairs $(X_{n,m},X_{n,m'})$ and $(X_{n+m},X_{n+m,m'-m})$ have the same distribution, and in particular
--   $$\mathbb E\Big[\big(f(X_{n,m'})-f(X_{n,m})\big)^2\Big]=\mathbb E\Big[\big(f(X_{n+m,m'-m})-f(X_{n+m})\big)^2\Big].$$
--
--   Shifting time by $m$ maps one pair of coupled chains onto another; this reduces every comparison of two past starts to a comparison with the chain started at $0$, where Assumption A1 applies.
--
--   Differences from the source:
--   - generalization: the equality of the two expectations → the identity in law of the pairs (X_{n,m}, X_{n,m′}) and (X_{n+m}, X_{n+m,m′−m}), together with the equality; reason: the proof on p.21 states the pair identity; it implies the printed equality, which is kept as the second conjunct
--   - encoding: X_{i,m} = G_{i+m}(X_0; U_{−m}, …, U_{i−1}) with i.i.d. U_i, i ∈ ℤ → `coupledChain g x₀ U i m` (the chain started from x₀ at integer time −m) inside the structure `ChainModel`; reason: the same random variables; `ChainModel` collects the standing assumptions of pp.2 and 4 (measurable g and f, i.i.d. noise on ℤ, f(X_i) square-integrable)
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), Proposition B.1, p.21

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_ChainModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace UnbiasedTimeAvg

/-- **Proposition B.1 (shift invariance of the coupled chains).** Kahalé, arXiv:2209.09581v1,
Proposition B.1, p.21: "For `n, m, m′ ∈ ℤ` with `n ≥ −m` and `n ≥ −m′`, we have
`E((f(X_{n,m′}) − f(X_{n,m}))²) = E((f(X_{n+m,m′−m}) − f(X_{n+m}))²)`."

The first conjunct is the identity in law of the pairs `(X_{n,m}, X_{n,m′})` and
`(X_{n+m}, X_{n+m,m′−m})` that the proof on p.21 establishes; the second is the printed equality.

**Formalization Note.** `X_{i,m}` is `coupledChain g x₀ U i m` (chain started from `x₀` at time
`−m`), `X_i = X_{i,0}`. Only the standing model (i.i.d. noise, measurable `g`, `f`) is assumed;
Assumption A1 is not used. -/
theorem proposition_B_1
    {Ω F F' : Type*} [MeasurableSpace Ω] [MeasurableSpace F] [MeasurableSpace F']
    {P : Measure Ω} [IsProbabilityMeasure P] {U : ℤ → Ω → F'} {g : F → F' → F} {f : F → ℝ}
    {x₀ : F} (hM : ChainModel P U g f x₀) (n m m' : ℤ) (hm : -m ≤ n) (hm' : -m' ≤ n) :
    IdentDistrib (fun ω => (coupledChain g x₀ U n m ω, coupledChain g x₀ U n m' ω))
      (fun ω => (coupledChain g x₀ U (n + m) 0 ω, coupledChain g x₀ U (n + m) (m' - m) ω)) P P ∧
    ∫ ω, (f (coupledChain g x₀ U n m' ω) - f (coupledChain g x₀ U n m ω)) ^ 2 ∂P =
      ∫ ω, (f (coupledChain g x₀ U (n + m) (m' - m) ω) - f (coupledChain g x₀ U (n + m) 0 ω)) ^ 2 ∂P := by sorry

end UnbiasedTimeAvg
