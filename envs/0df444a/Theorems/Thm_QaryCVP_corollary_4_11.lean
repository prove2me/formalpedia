-- Prove2me | Theorems.Thm_QaryCVP_corollary_4_11
-- name    : QaryCVP.corollary_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:59:59.8822+00:00
-- url     : https://prove2.me/theorems/1903f715-06db-45d9-b726-e5e17ed3f1ae
-- title:
--   Corollary 4.11 — Algorithm 3 for $1<\delta\le3/2$, $q\ge3$: time $2^{0.56n+o(n)}$, space $2^{0.325n+o(n)}$, with the 5/3-CVP guarantee
-- statement:
--   There is a program $P$ (Algorithm 3 with $\gamma=5/3$ and its parameters for this density range) such that:
--
--   1. for integers $q\ge3$, $n\ge1$, $m\ge1$ with $1<\delta\le3/2$, on every input matrix, rational target and execution, $P$ runs in bit time $2^{T_>(\delta)n+o(n)}$ and bit space $2^{S_>(\delta)n+o(n)}$, uniformly over the density interval, and in particular in time $2^{0.56n+o(n)}$ and space $2^{0.325n+o(n)}$, up to a polynomial factor in the binary input length;
--   2. its simultaneous success guarantee for 5/3-CVP is that of Theorem 4.7: for all sufficiently large $n$ and all such $q,m$, all but a $2^{-\Omega(n^{2/3})}$ fraction of $H$ satisfy: with probability at least $1-2^{-\Omega(n)}$ over the coins, $P$ solves 5/3-CVP for every $y\in\mathbb Q^n$ simultaneously.
--
--   This gives the second row of Theorem 1.1 for $q\ge3$.
--
--   **Formalization Note** $q$ is not restricted to be odd or prime. $T_>(\delta)$, $S_>(\delta)$ are (32) at the limiting proportions (13).
--
--   Differences from the source:
--   - reading: the procedure (a specific algorithm of the paper) → there is a program of the RAM with every stated property, bundled for the same program; reason: decision 3: writing the algorithm as RAM code inside a statement is not feasible; the bundle carries every property later steps use
--   - reading: time and space in bit operations and bits, no machine named (p.13) → bit time and bit space of the published randomized log-cost rational RAM TwMSOCount.Main; reason: the paper's cost model; this machine charges bit operations at least as heavily (decision 1)
--   - reading: factors polynomial in the binary input length → (ℓ+1)^K with ℓ the total bit length of the input word and K fixed before the input; reason: p.13: poly is a polynomial in the binary input length
--   - reading: o(n) in the exponent → one g : ℕ → ℝ with g(n)/n → 0, fixed before the input; reason: p.13 asymptotic convention; one g for all clauses is the stronger form
--   - reading: on every input and execution → the run halts on every coin tape and the bounds hold on every tape; reason: p.13, Theorem 1.1
--   - reading: 1 < δ ≤ 3/2 → q^m > 2^n and q^{2m} ≤ 2^{3n}; reason: exact integer tests, as Algorithm 3 uses (R8)
--   - reading: all but a 2^{−Ω(f(n))} fraction / probability 1 − 2^{−Ω(f(n))} → ∃ c > 0 and a threshold N with fraction (resp. probability) ≥ 1 − 2^{−c f(n)} for n ≥ N; reason: p.12 definition of Ω for sufficiently large n (R4)
--   - encoding: fraction of matrices → count of matrices with the property divided by q^{mn}, as a real number; reason: R5; same instances
--   - encoding: probability of an event of the coin tape → fair-coin measure of the event, with its measurability a clause of the conclusion; reason: the event is defined from a program run; measurability makes the probability meaningful
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Corollary 4.11, p.46; (32), p.46; (13)–(14), p.34; Theorem 4.7, p.39

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_matAvg
import Definitions.Def_QaryCVP_encInst
import Definitions.Def_QaryCVP_ent3

open MeasureTheory Filter Topology TwMSOCount.Main
open scoped ENNReal

namespace QaryCVP

/-- **Corollary 4.11** (costs for density between one and three halves, with the simultaneous
5/3-CVP guarantee). Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4),
Corollary 4.11, p.46; (32), p.46; (13)–(14), p.34; Theorem 4.7, p.39.

There is a program `P` (Algorithm 3 with `γ = 5/3` and its parameters for this density range) such
that:

1. for integers `q ≥ 3`, `n ≥ 1`, `m ≥ 1` with `1 < δ ≤ 3/2`, on every input matrix, rational target
   and execution, `P` runs in bit time `2^{T_>(δ)n + o(n)}` and bit space `2^{S_>(δ)n + o(n)}`,
   uniformly over the density interval, and in particular in bit time `2^{0.56n + o(n)}` and bit
   space `2^{0.325n + o(n)}`, up to a polynomial factor in the binary input length;
2. its simultaneous success guarantee for 5/3-CVP is that of Theorem 4.7: for all sufficiently large
   `n` and all such `q, m`, all but a `2^{−Ω(n^{2/3})}` fraction of `H` satisfy: with probability at
   least `1 − 2^{−Ω(n)}` over the coins, `P` solves 5/3-CVP for every `y ∈ Qⁿ` simultaneously.

**Formalization Note.** Decision 3 (existential form; the parameters (13)–(14) are internal to `P`,
and `q` is not restricted to be odd or prime). `δ = m log₂ q / n`; `1 < δ ≤ 3/2` is tested exactly as
`qᵐ > 2ⁿ`, `q^{2m} ≤ 2^{3n}` (R8). `T_>(δ)`, `S_>(δ)` are (32) at the limiting proportions (13)
(`θ = 0`). One `g` with `g(n)/n → 0` (R3); `poly` is `(ℓ+1)^K` (R2). -/
theorem corollary_4_11 :
    ∃ (P : Program) (g : ℕ → ℝ) (K : ℕ), Tendsto (fun n => g n / n) atTop (𝓝 0) ∧
      (∀ n m q : ℕ, 1 ≤ n → 3 ≤ q → 1 ≤ m → ¬ DensityLeOne q m n →
        DensityLeThreeHalves q m n →
        ∀ (H : Matrix (Fin m) (Fin n) (ZMod q)) (y : Fin n → ℚ),
          RunsWithin P (encInst H y)
            ((2 : ℝ) ^ (Tgt (density q m n) 0 * n + g n) * polyF K (encInst H y))
            ((2 : ℝ) ^ (Sgt (density q m n) 0 * n + g n) * polyF K (encInst H y)) ∧
          RunsWithin P (encInst H y)
            ((2 : ℝ) ^ (56 / 100 * n + g n) * polyF K (encInst H y))
            ((2 : ℝ) ^ (325 / 1000 * n + g n) * polyF K (encInst H y))) ∧
      (∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ N : ℕ, ∀ n m q : ℕ, N ≤ n → 3 ≤ q → 1 ≤ m →
        ¬ DensityLeOne q m n → DensityLeThreeHalves q m n →
        1 - (2 : ℝ) ^ (-c₁ * (n : ℝ) ^ ((2 : ℝ) / 3)) ≤
          matFrac q m n (fun H => GoodMatrix P (5 / 3) H ((2 : ℝ) ^ (-c₂ * n)))) := by sorry

end QaryCVP
