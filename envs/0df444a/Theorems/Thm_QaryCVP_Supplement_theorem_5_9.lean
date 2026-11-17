-- Prove2me | Theorems.Thm_QaryCVP_Supplement_theorem_5_9
-- name    : QaryCVP.Supplement.theorem_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:16:55.805212+00:00
-- url     : https://prove2.me/theorems/312799fc-f39a-4e1c-bfbb-eb5e49d0a9db
-- title:
--   Theorem 5.9 — SVP at bounded density: for each row $(D,T,S)$ of Table 2, time $2^{Tn+o(n)}$, space $2^{Sn+o(n)}$, shortest with probability $1-2^{-\Omega(n)}$
-- statement:
--   For each row $(D,T,S)$ of Table 2,
--
--   | $D$ | $T$ | $S$ |
--   |---|---|---|
--   | 1 | 0.27400949 | 0.261392024 |
--   | 1.05 | 0.286 | 0.270 |
--   | 1.10 | 0.298 | 0.276 |
--   | 1.20 | 0.326 | 0.286 |
--   | 1.30 | 0.361 | 0.309 |
--   | 1.40 | 0.408 | 0.320 |
--   | 1.50 | 0.468 | 0.329 |
--
--   there is one randomized algorithm (Algorithm 4 with a parameter choice) such that for all integers $q\ge2$, $n\ge1$, $m\ge0$ with $0\le\delta=m\log_2q/n\le D$:
--
--   1. every execution on every input matrix $H$ returns a nonzero vector of $\Lambda$, takes time $2^{Tn+o(n)}$ and uses space $2^{Sn+o(n)}$, omitting factors polynomial in the binary input length;
--   2. for sufficiently large $n$, all but a $2^{-\Omega(n^{2/3})}$ fraction of uniform matrices $H$ satisfy, with $H$ held fixed,
--
--   $$\Pr\big[\text{the returned vector is a shortest nonzero vector of }\Lambda\big]\ \ge\ 1-2^{-\Omega(n)}$$
--
--   over the algorithm's randomness.
--
--   Theorem 5.9 is the formal version of the paper's headline SVP result (Theorem 1.2); its first row is the bound $2^{0.27400949n+o(n)}$ at density at most one.
--
--   **Formalization Note** The decimals are exact rationals; the first row uses the eight-digit constants, not the rounded ones of Theorem 1.2.
--
--   Differences from the source:
--   - reading: there is a parameter choice for Algorithm 4 with the stated properties → there is one program of the RAM with all stated properties (nonzero output on every tape, time, space, success), bundled; reason: base decision 3 (existential form, as the base goal Theorem 1.1); the bundle with the success clause excludes trivial programs (qe1 is always a nonzero lattice vector)
--   - reading: time and space in bit operations and bits, no machine named (p.13) → bit time and bit space of the published randomized log-cost rational RAM TwMSOCount.Main; reason: base decision 1 (R1); this machine charges bit operations at least as heavily
--   - reading: factors polynomial in the binary input length → (ℓ+1)^K with ℓ the total bit length of the input word and K fixed before the input; reason: p.13 (base R2)
--   - reading: o(n) in the exponent → one g : ℕ → ℝ with g(n)/n → 0, fixed before the input, shared by time and space; reason: p.13 asymptotic convention (base R3); one g is the stronger form
--   - reading: on every input (every execution) → the run halts on every coin tape and the bounds hold on every tape; reason: p.13 and Theorem 5.9 "Every execution" (base R10)
--   - reading: Input: H ∈ (Z/qZ)^{m×n} → the input word n, m, q, then the entries of H row by row as canonical representatives in [0, q) (encSVP); reason: base R9 without a target
--   - encoding: δ = m log q / n ≤ D → the real density m log₂ q / n ≤ D (QaryCVP.density); reason: the same condition; D is a real constant
--   - encoding: a shortest nonzero vector, ‖x‖ = min_{a∈Λ∖{0}} ‖a‖ → x ∈ Λ, x ≠ 0 and ‖x‖² ≤ ‖a‖² for every nonzero a ∈ Λ; reason: squared form (base R7); the minimum exists since Λ ⊇ qZⁿ is discrete
--   - reading: all but a 2^{−Ω(f(n))} fraction / probability 1 − 2^{−Ω(f(n))}, for sufficiently large n → ∃ c > 0 and a threshold N, uniform in q and m, with fraction (resp. probability) ≥ 1 − 2^{−c f(n)} for n ≥ N; reason: p.12 definition of Ω for sufficiently large n (base R4)
--   - encoding: fraction of uniform matrices H → count of matrices with the property divided by q^{mn}, as a real number; reason: base R5; same instances
--   - encoding: probability over the algorithm's randomness → fair-coin measure of the success event, with its measurability a clause (GoodMatrixSVP); reason: the event is defined from a program run; measurability makes the probability meaningful
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Theorem 5.9, p.57 (PDF 58); Table 2, p.56 (PDF 57)

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_matAvg
import Definitions.Def_QaryCVP_encInst
import Definitions.Def_QaryCVP_Supplement_svpBasics
import Definitions.Def_QaryCVP_Supplement_svpExponents

open MeasureTheory Filter Topology TwMSOCount.Main

namespace QaryCVP.Supplement

/-- **Theorem 5.9** (SVP at bounded density). Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript
(sha256 9aeb2ff4…ab4), Theorem 5.9, p.57; Table 2, p.56.

For each row `(D, T, S)` of Table 2 there is one randomized program `Pr` of the log-cost RAM
(Algorithm 4 with a parameter choice) such that, for all integers `q ≥ 2`, `n ≥ 1`, `m ≥ 0` with
`0 ≤ δ ≤ D`:

1. on every input matrix and every execution, `Pr` returns a nonzero vector of `Λ`, in time
   `2^{Tn + o(n)}` and space `2^{Sn + o(n)}`, up to a polynomial factor in the binary input length;
2. for sufficiently large `n`, all but a `2^{−Ω(n^{2/3})}` fraction of uniform `H` have the property
   that, with `H` fixed, with probability at least `1 − 2^{−Ω(n)}` over the coins, the returned vector
   is a shortest nonzero vector of `Λ`.

**Formalization Note.** Base decision 3: "there is a parameter choice for Algorithm 4" is stated as
the existence of one program with all the properties, bundled (as the base goal Theorem 1.1). The
machine is `TwMSOCount.Main` (R1); `o(n)` is one `g` with `g(n)/n → 0` (R3); polynomial factors are
`(ℓ+1)^K` (R2); `2^{−Ω(·)}` is `∃ c > 0, N` uniform in `q, m` (R4); fractions count matrices (R5);
`δ ≤ D` is the real density `m log₂ q / n ≤ D`. -/
theorem theorem_5_9 :
    ∀ row ∈ table2,
      ∃ (Pr : Program) (g : ℕ → ℝ) (K : ℕ) (c₁ c₂ : ℝ) (N : ℕ),
        Tendsto (fun n => g n / n) atTop (𝓝 0) ∧ 0 < c₁ ∧ 0 < c₂ ∧
        (∀ n m q : ℕ, 1 ≤ n → 2 ≤ q → density q m n ≤ (row.1 : ℝ) →
          ∀ H : Matrix (Fin m) (Fin n) (ZMod q),
            AlwaysNonzero Pr H ∧
            RunsWithin Pr (encSVP H)
              ((2 : ℝ) ^ ((row.2.1 : ℝ) * n + g n) * polyF K (encSVP H))
              ((2 : ℝ) ^ ((row.2.2 : ℝ) * n + g n) * polyF K (encSVP H))) ∧
        (∀ n m q : ℕ, N ≤ n → 2 ≤ q → density q m n ≤ (row.1 : ℝ) →
          1 - (2 : ℝ) ^ (-c₁ * (n : ℝ) ^ ((2 : ℝ) / 3)) ≤
            matFrac q m n (fun H => GoodMatrixSVP Pr H ((2 : ℝ) ^ (-c₂ * n)))) := by sorry

end QaryCVP.Supplement
