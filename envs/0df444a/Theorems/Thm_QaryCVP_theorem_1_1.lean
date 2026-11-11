-- Prove2me | Theorems.Thm_QaryCVP_theorem_1_1
-- name    : QaryCVP.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:59:52.745843+00:00
-- url     : https://prove2.me/theorems/b36339ed-382c-4720-8bb4-c796f9754408
-- title:
--   Theorem 1.1 — 5/3-CVP on random q-ary lattices for every rational target, time $2^{0.2668n+o(n)}$ ($\delta\le1$) and $2^{0.56n+o(n)}$ ($\delta\le3/2$)
-- statement:
--   For an integer modulus $q\ge2$ and $H\in(\mathbb Z/q\mathbb Z)^{m\times n}$ let $\Lambda=\{x\in\mathbb Z^n:Hx\equiv0\pmod q\}$ and $\delta=m\log_2q/n$. There is one randomized algorithm (a program of the log-cost RAM) such that, uniformly over all $q\ge2$, for $0\le\delta\le3/2$:
--
--   1. given $H$ and $y\in\mathbb Q^n$, on every input and execution it has
--
--   | density | time | space |
--   |---|---|---|
--   | $0\le\delta\le1$ | $2^{0.2668n+o(n)}$ | $2^{0.2628n+o(n)}$ |
--   | $1<\delta\le3/2$ | $2^{0.56n+o(n)}$ | $2^{0.325n+o(n)}$ |
--
--   up to factors polynomial in the binary input length;
--   2. for sufficiently large $n$, all but a $2^{-\Omega(n^{2/3})}$ fraction of matrices $H$ have the following property: with $H$ held fixed, with probability at least $1-2^{-\Omega(n)}$ over the internal randomness, the algorithm outputs $x\in\Lambda$ satisfying
--
--   $$\|x-y\|\le\tfrac53\min_{v\in\Lambda}\|v-y\|$$
--
--   simultaneously for every $y\in\mathbb Q^n$.
--
--   The guarantee holds for every rational target, including targets chosen after $H$ is known.
--
--   **Formalization Note** One coin tape serves every target: the success event is the set of tapes on which the output is a 5/3-approximation for all $y$ at once, and it is measurable. The approximation is stated squared, $\|x-y\|^2\le\frac{25}{9}\|a-y\|^2$ for every $a\in\Lambda$. The decimals are exact rationals.
--
--   Differences from the source:
--   - reading: time and space in bit operations and bits, no machine named (p.13) → bit time and bit space of the published randomized log-cost rational RAM TwMSOCount.Main; reason: the paper's cost model; this machine charges bit operations at least as heavily (decision 1)
--   - reading: factors polynomial in the binary input length → (ℓ+1)^K with ℓ the total bit length of the input word and K fixed before the input; reason: p.13: poly is a polynomial in the binary input length
--   - reading: o(n) in the exponent → one g : ℕ → ℝ with g(n)/n → 0, fixed before the input; reason: p.13 asymptotic convention; one g for all clauses is the stronger form
--   - reading: on every input and execution → the run halts on every coin tape and the bounds hold on every tape; reason: p.13, Theorem 1.1
--   - reading: there is a randomized algorithm → there is one program P of the RAM, fixed before n, m, q, H, y and the tape; reason: decision 6: one algorithm for all inputs
--   - reading: for sufficiently large n, all but a 2^{−Ω(n^{2/3})} fraction … with probability at least 1 − 2^{−Ω(n)} → ∃ c₁, c₂ > 0 and N, uniform in q ≥ 2 and m, with fraction ≥ 1 − 2^{−c₁ n^{2/3}} of H whose success probability is ≥ 1 − 2^{−c₂ n}; reason: R4; 'bounds uniform over all integer moduli q ≥ 2' (p.2)
--   - reading: simultaneously for every y ∈ Qⁿ → the event {τ : ∀ y, P on (H, y) with tape τ outputs a 5/3-approximation}, measurable; reason: R6: one execution's randomness for all targets
--   - encoding: ‖x − y‖ ≤ (5/3) min_{v∈Λ} ‖v − y‖ → x ∈ Λ and ‖x − y‖² ≤ (25/9)‖a − y‖² for every a ∈ Λ; reason: R7: the minimum exists; same instances
--   - encoding: 0 ≤ δ ≤ 1 and 1 < δ ≤ 3/2 → q^m ≤ 2^n, resp. q^m > 2^n and q^{2m} ≤ 2^{3n}; reason: R8: exact integer tests
--   - encoding: given H and y → the input word n, m, q, the entries of H as representatives in [0, q), then y₁, …, yₙ; reason: R9
--   - encoding: fraction of matrices → count of matrices with the property divided by q^{mn}, as a real number; reason: R5; same instances
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Theorem 1.1, p.2 (uniformity sentence, p.2; formal content §4, pp.33–46)

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_matAvg
import Definitions.Def_QaryCVP_encInst

open MeasureTheory Filter Topology TwMSOCount.Main
open scoped ENNReal

namespace QaryCVP

/-- **Theorem 1.1** (5/3-CVP on random q-ary lattices). Kim, Kwon, Lee, Lee, *Fast Provable
Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices*, STOC 2027 submission
manuscript (sha256 9aeb2ff4…ab4), Theorem 1.1, p.2 (table and uniformity sentence, p.2; formal
content §4, pp.33–46).

There is one randomized program `P` of the log-cost RAM such that, uniformly over all integer
moduli `q ≥ 2`, for `0 ≤ δ = m log₂ q / n ≤ 3/2`:

1. given `H ∈ (Z/qZ)^{m×n}` and `y ∈ Qⁿ`, on every input and every execution `P` runs in bit time
   `2^{0.2668n + o(n)}` and bit space `2^{0.2628n + o(n)}` if `0 ≤ δ ≤ 1`, and in bit time
   `2^{0.56n + o(n)}` and bit space `2^{0.325n + o(n)}` if `1 < δ ≤ 3/2`, up to a polynomial factor in
   the binary input length;
2. for sufficiently large `n`, all but a `2^{−Ω(n^{2/3})}` fraction of matrices `H` have the
   property that, with `H` fixed, with probability at least `1 − 2^{−Ω(n)}` over the internal
   randomness, `P` outputs `x ∈ Λ` with `‖x − y‖ ≤ (5/3) min_{v∈Λ} ‖v − y‖` simultaneously for every
   `y ∈ Qⁿ`.

**Formalization Note.** The machine is the published randomized log-cost rational RAM
`TwMSOCount.Main` (bit time; bit space; fair coin tape) (R1). `o(n)` is one `g` with `g(n)/n → 0`,
shared by both rows, fixed before the input (R3); polynomial factors are `(ℓ + 1)^K` with `ℓ` the
binary input length (R2). `2^{−Ω(·)}` is `∃ c₁, c₂ > 0, N`, uniform in `q` and `m` (R4). The
fraction counts matrices among the `q^{mn}` (R5). One coin tape serves every target: the success
event is `{τ : ∀ y, …}`, and it is measurable (R6). The approximation is squared:
`‖x − y‖² ≤ (25/9)‖a − y‖²` for every `a ∈ Λ` (R7). `δ ≤ 1` and `δ ≤ 3/2` are tested exactly as
`qᵐ ≤ 2ⁿ` and `q^{2m} ≤ 2^{3n}` (R8). The input word lists `n, m, q`, the entries of `H` and of `y`
(R9). The decimals are exact rationals. -/
theorem theorem_1_1 :
    ∃ (P : Program) (g : ℕ → ℝ) (K : ℕ) (c₁ c₂ : ℝ) (N : ℕ),
      Tendsto (fun n => g n / n) atTop (𝓝 0) ∧ 0 < c₁ ∧ 0 < c₂ ∧
      (∀ n m q : ℕ, 1 ≤ n → 2 ≤ q → DensityLeThreeHalves q m n →
        ∀ (H : Matrix (Fin m) (Fin n) (ZMod q)) (y : Fin n → ℚ),
          (DensityLeOne q m n →
            RunsWithin P (encInst H y)
              ((2 : ℝ) ^ (2668 / 10000 * n + g n) * polyF K (encInst H y))
              ((2 : ℝ) ^ (2628 / 10000 * n + g n) * polyF K (encInst H y))) ∧
          (¬ DensityLeOne q m n →
            RunsWithin P (encInst H y)
              ((2 : ℝ) ^ (56 / 100 * n + g n) * polyF K (encInst H y))
              ((2 : ℝ) ^ (325 / 1000 * n + g n) * polyF K (encInst H y)))) ∧
      (∀ n m q : ℕ, N ≤ n → 2 ≤ q → DensityLeThreeHalves q m n →
        1 - (2 : ℝ) ^ (-c₁ * (n : ℝ) ^ ((2 : ℝ) / 3)) ≤
          matFrac q m n (fun H => GoodMatrix P (5 / 3) H ((2 : ℝ) ^ (-c₂ * n)))) := by sorry

end QaryCVP
