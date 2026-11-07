-- Prove2me | Theorems.Thm_TIEMaximin_theorem_1_1
-- name    : TIEMaximin.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:42:55.902636+00:00
-- url     : https://prove2.me/theorems/8a504a4e-875b-47af-9c92-eedc42c26613
-- title:
--   Theorem 1.1 — a TIE, ex-ante envy-free mechanism with $v_i(A_i)\ge\mathrm{TPS}_i/6\ge\mathrm{MMS}_i/6$ in every realized allocation
-- statement:
--   Consider $m$ indivisible goods and $n$ agents with nonnegative additive valuations. There is a randomized mechanism that is truthful in expectation and ex-ante envy-free, and such that at every nonnegative profile every allocation $A$ in the support of its output satisfies, for every agent $i$,
--
--   $$v_i(A_i)\ge\frac{\mathrm{TPS}_i}{6}\ge\frac{\mathrm{MMS}_i}{6}.$$
--
--   For rational valuations encoded in binary, an explicit lottery over at most $m(n-1)+1$ complete allocations implementing the mechanism can be computed in polynomial time: one Turing machine, for all $n$ and $m$, outputs on every nonnegative rational profile a list of at most $m(n-1)+1$ weighted allocations whose weights are exactly the lottery of the mechanism.
--
--   The factor $1/6$ depends on neither the number of agents nor the number of goods. This is the first constant ex-post maximin-share guarantee for truthful-in-expectation mechanisms with an arbitrary number of agents.
--
--   Differences from the source:
--   - reading: can be computed in polynomial time, for rational valuations encoded in binary → one machine `alg` with `Nonempty (Turing.TM2ComputableInPolyTime encMechIn encLottery alg)`, for all n and m; reason: a polynomial-time algorithm is uniform in the input; Mathlib's Turing-machine model on the binary encoding of (n, m, profile)
--   - reading: Consider m goods and n agents; there is a mechanism → one mechanism per (n, m), quantified after the machine; reason: the mechanism's domain depends on (n, m)
--   - encoding: n agents → `0 < n`; reason: no allocation exists for n = 0 < m
--   - encoding: output of the algorithm → a list of (rational weight, allocation word); `IsLotteryList`, `listWeight`, and `M(v)` given by these weights; malformed encoded inputs may get any output; reason: same lotteries; entries may repeat and their weights add up
--   - encoding: allocations; agents N, goods M; nonnegative additive valuations; lotteries → maps `Fin m → Fin n`; `Fin n`, `Fin m`; real matrices with `Nonneg`; `PMF`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_TIEMaximin_Mechanism
import Definitions.Def_TIEMaximin_Encoding

namespace TIEMaximin

/-- **Theorem 1.1 (Main theorem)** (p.2). Consider `m` indivisible goods and `n` agents with
nonnegative additive valuations. There is a randomized mechanism that is truthful-in-expectation
and ex-ante envy-free, and such that every allocation `A` in the support of its output satisfies,
for every agent `i`, `v_i(A_i) ≥ TPS_i/6 ≥ MMS_i/6`. For rational valuations encoded in binary, an
explicit lottery over at most `m(n − 1) + 1` complete allocations implementing the mechanism can
be computed in polynomial time.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Theorem 1.1, p.2.

**Formalization Note.** One machine `alg` serves all `n` and `m` (a polynomial-time algorithm is
uniform), and the mechanism is quantified per `(n, m)`, after it. Polynomial time is
`Turing.TM2ComputableInPolyTime` over the binary encodings `encMechIn`, `encLottery`. On every
nonnegative rational profile, the output is a well-formed list of at most `m(n − 1) + 1`
allocations and its weights are exactly the lottery `M(v)`; malformed encoded inputs may get any
output. `0 < n`, because for `n = 0 < m` no allocation exists. Valuations are real matrices, every
property quantifying over nonnegative ones. -/
theorem theorem_1_1 :
    ∃ alg : MechIn → List (ℚ × List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encMechIn encLottery alg) ∧
      ∀ n m : ℕ, 0 < n →
        ∃ M : Mech n m,
          IsTIE M ∧ IsExAnteEF M ∧
          (∀ v, Nonneg v → ∀ A ∈ (M v).support, ∀ i,
            tps n (v i) / 6 ≤ valOf (v i) i A ∧ mmsOf n (v i) / 6 ≤ tps n (v i) / 6) ∧
          ∀ v : Fin n → Fin m → ℚ, (∀ i g, 0 ≤ v i g) →
            IsLotteryList n m (alg (mkIn n m v)) ∧
            (alg (mkIn n m v)).length ≤ m * (n - 1) + 1 ∧
            ∀ A, ((M fun i g => ((v i g : ℚ) : ℝ)) A).toReal = listWeight (alg (mkIn n m v)) A := by sorry

end TIEMaximin
