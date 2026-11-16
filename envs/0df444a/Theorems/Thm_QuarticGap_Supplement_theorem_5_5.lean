-- Prove2me | Theorems.Thm_QuarticGap_Supplement_theorem_5_5
-- name    : QuarticGap.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:56:33.033918+00:00
-- url     : https://prove2.me/theorems/7d4735e6-8e9e-483a-993c-fd72392218cc
-- title:
--   Theorem 5.5 — analytic matrix functions $g(P_W)b$: $\Omega(n^2/\log n)$ classical, $\widetilde O(\sqrt n)$ quantum, $\Omega(\sqrt n)$ if $a_1 \ne 0$
-- statement:
--   Let $g$ be analytic on the disk $\{z\in\mathbb C : |z-1| < r_g\}$, write $g(1+z) = \sum_{k\ge0}a_kz^k$, fix $t_* \in (0,1/64]$ with $9t_* < r_g$, and let $A_g, B_g, L_g, L_g', K_g, c_g, M_g$ be the constants (19). Suppose $a_0 \ne 0$ and $a_2 \ne 0$, and let $t \in (0, t_*]$ be a rational number with
--   $$
--   128K_gt^2 \le |a_0|^2,\qquad M_gt^2 \le \frac{c_g}{12}. \tag{20}
--   $$
--   For every constant $\varepsilon \in (0, c_gt^4/4)$ there are $c > 0$, $C > 0$ and $n_0$ such that, for every power of four $n \ge n_0$:
--
--   1. every classical algorithm with access $\mathrm{SQ}(P_W)$ that samples from $p_{g(P_W)b}$ within total variation distance $\varepsilon$ for every $W \in \mathcal G$ makes more than $cn^2/\log n$ queries on some $W \in \mathcal G$, and more than $cn^2/\log n$ queries in expectation on some $W\in\mathcal G$;
--   2. a quantum algorithm over $\{H, T, \mathrm{CNOT}\}$ solves the task with at most $C\sqrt n(\log n)^C$ queries and gates;
--   3. if moreover $a_1 \ne 0$ and
--   $$
--   L_g't^2 \le \frac{|a_1|}{2},\qquad t^2 \le \frac{2|a_1|^2}{5|a_2|^2}, \tag{21}
--   $$
--   then every quantum algorithm for the task makes at least $c\sqrt n$ queries.
--
--   The theorem covers ridge regression, matrix powers, square roots and real- and imaginary-time evolution (Table 3).
--
--   **Formalization Note** $g(P_W) = \sum_k a_k(-tT_W)^k$, the matrix function on $\mathcal G$; $g$ may be complex valued. Quantum access is to the zero-padded $P_W$ (Remark 4.4).
--
--   Differences from the source:
--   - encoding: n a power of four, positions in {0,1}^k → n = 4^ℓ, positions in {0,1}^{2ℓ}, √n = 2^ℓ; reason: the same values of n
--   - reading: a randomized classical algorithm → QueryAlg, a behaviour strategy on transcripts with unrestricted computation; reason: an algorithm with private coins and perfect recall has a behaviour strategy with the same law (Kuhn); the input reaches it only through the answers
--   - encoding: output distribution within total variation distance ε → sampleErr, which counts the mass of non-halting runs as an extra outcome; reason: it is TV for an algorithm that halts almost surely and gives a non-halting algorithm no advantage
--   - encoding: coherent access to the 3n × 3n (or (3n+1) × (3n+1)) matrix → coherent access to the matrix zero padded to 4n × 4n, quantum outputs in the 4n padded coordinates with the target padded by zeros; reason: Remark 4.4 (p.32): the padded rows and columns are zero and known and the targets vanish on them; an output on a padding coordinate only adds error
--   - reading: a fixed binary encoding of the entries → the published ratEnc: sign bit, numerator and denominator in 2ℓ + 2 + size(|num t|·den t) bits; reason: every entry is rational with numerator and denominator of O(log n) bits (§2.4, p.17); the width fits all of them exactly
--   - reading: a quantum algorithm → an oracle circuit on any number of wires, started in |0⟩ and measured at the end, fixed before W and the oracles and correct for every legal choice of the input operations; reason: Definition 2.2: an algorithm must succeed for every choice of the unspecified action; the base goal's convention
--   - reading: quantum query complexity Θ̃(√n) → one circuit over {H, T, CNOT} with at most C√n(log n)^C queries, output reading wires, and at least c√n queries for every circuit over all unitary gates with any output map; reason: the proof's Lemma 2.10 gives Ω(√n) and §5 (p.33) says Θ̃(ρ) queries suffice and are necessary; the stronger reading of the lower bound
--   - reading: Õ(√n) gates → at most C√n(log n)^C gates from {H, T, CNOT}, oracle calls not counted, by the same circuit; reason: the proof synthesizes rotations over a finite universal gate set (Lemma 2.9 with [RS16]); the base goal's convention
--   - encoding: g(P_W), the matrix function → the power series ∑_k a_k (−tT_W)^k; reason: the source's own expansion (p.35); on G it converges absolutely to the matrix function since ∥tT_W∥ ≤ 9t < r_g, and only W ∈ G is used
--   - encoding: the series (19) with k from 1 or 2 → tsums of nonnegative reals reindexed from k = 0; reason: the same sums; they converge since √65 t∗ < 9t∗ < r_g
--   - encoding: g analytic on the open disk, r_g > 0 → AnalyticOnNhd on Metric.ball 1 r_g; r_g > 0 not a separate binder; reason: on an open set analyticity at every point is the same; 0 < 9t∗ < r_g implies r_g > 0
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Theorem 5.5 with (19)–(21), pp.35–36

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QuarticGap_Supplement_matFun

open QAlgorithms

namespace QuarticGap.Supplement

/-- Theorem 5.5 (arXiv:2610.42069 (file sha256 9f68aaf9…), pp.35–36). Let `g` be analytic on the disk
`{z ∈ ℂ : |z − 1| < r_g}`, `r_g > 0`, with Taylor coefficients `g(1 + z) = ∑_k a_k z^k`; fix
`t∗ ∈ (0, 1/64]` with `9t∗ < r_g`, and let `A_g, B_g, L_g, L′_g, K_g, c_g, M_g` be as in (19). Let
`a₀ ≠ 0`, `a₂ ≠ 0`, and let `t ∈ (0, t∗]` be a rational number with
`128 K_g t² ≤ |a₀|²` and `M_g t² ≤ c_g/12` (20). For every constant `ε ∈ (0, c_g t⁴/4)`, there are
`c > 0` and `n₀` such that, for every power of four `n ≥ n₀`, every classical algorithm that samples
from `p_{g(P_W)b}` within total variation distance `ε` for every `W ∈ G` makes more than `cn²/log n`
queries on some `W ∈ G`, and more than `cn²/log n` queries in expectation on some `W ∈ G`. A quantum
algorithm solves the task with `Õ(√n)` queries and gates. If moreover `a₁ ≠ 0` and
`L′_g t² ≤ |a₁|/2`, `t² ≤ 2|a₁|²/(5|a₂|²)` (21), then every quantum algorithm for the task makes
`Ω(√n)` queries.

**Formalization Note** `n = 4^ℓ`; `g` may be complex valued; `g(P_W)` is the power series
`∑_k a_k (−tT_W)^k`, which on `G` converges to the matrix function. The models are those of the
published goal: classical `QueryAlg` against `SQ(P_W)` on the `3n × 3n` matrix; quantum circuits with
access to `P_W` zero padded to `4n × 4n` (Remark 4.4). The upper bound is one circuit over
`{H, T, CNOT}`, fixed before `W` and the oracles, with at most `C√n(log n)^C` queries and gates; the
lower bound, under the extra hypotheses `a₁ ≠ 0` and (21) only, is `c√n` queries for every circuit
over all unitary gates with any output map. `c`, `C`, `n₀` come after `g`, `t∗`, `t`, `ε`. The source's `r_g > 0` is implied by
`0 < 9t∗ < r_g` and is not repeated. -/
theorem theorem_5_5 (g : ℂ → ℂ) (rg : ℝ)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 1 rg)) (ts : ℝ) (hts : 0 < ts ∧ ts ≤ 1 / 64)
    (htsr : 9 * ts < rg) (ha0 : taylorA g 0 ≠ 0) (ha2 : taylorA g 2 ≠ 0)
    (t : ℚ) (ht : 0 < t ∧ (t : ℝ) ≤ ts)
    (h20a : 128 * Kg g ts * (t : ℝ) ^ 2 ≤ ‖taylorA g 0‖ ^ 2)
    (h20b : Mg g ts * (t : ℝ) ^ 2 ≤ cg g / 12)
    (ε : ℝ) (hε : 0 < ε ∧ ε < cg g * (t : ℝ) ^ 4 / 4) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ ℓ : ℕ, n₀ ≤ 4 ^ ℓ →
      (∀ alg : QueryAlg (SQQuery (Ix3 ℓ) (Ix3 ℓ)) (SQAns (Ix3 ℓ) (Ix3 ℓ)) (Ix3 ℓ),
        (∀ W ∈ G ℓ, alg.sampleErr (pRespond t W) (lenSqDist (gVec g t W)) ≤ ε) →
        (∃ W ∈ G ℓ, ¬ alg.MakesAtMostReal (pRespond t W)
          (c * ((4 : ℝ) ^ ℓ) ^ 2 / Real.log ((4 : ℝ) ^ ℓ))) ∧
        (∃ W ∈ G ℓ, ENNReal.ofReal (c * ((4 : ℝ) ^ ℓ) ^ 2 / Real.log ((4 : ℝ) ^ ℓ)) <
          alg.expQueries (pRespond t W))) ∧
      (∃ (N : ℕ) (alg : OracleCircuit htcxGateSet (supArity ℓ t) N)
          (w : Fin (2 + 2 * ℓ) ↪ Fin N),
        (totalQueries alg : ℝ) ≤ C * Real.sqrt ((4 : ℝ) ^ ℓ) * Real.log ((4 : ℝ) ^ ℓ) ^ C ∧
        (alg.gateCount : ℝ) ≤ C * Real.sqrt ((4 : ℝ) ^ ℓ) * Real.log ((4 : ℝ) ^ ℓ) ^ C ∧
        ∀ W ∈ G ℓ, ∀ orc, IsPAccess t W orc →
          tv (qOut alg orc (readWires w)) (lenSqDist (padVec dec3 (gVec g t W))) ≤ ε) ∧
      (taylorA g 1 ≠ 0 → Lg' g ts * (t : ℝ) ^ 2 ≤ ‖taylorA g 1‖ / 2 →
        (t : ℝ) ^ 2 ≤ 2 * ‖taylorA g 1‖ ^ 2 / (5 * ‖taylorA g 2‖ ^ 2) →
        ∀ (N : ℕ) (alg : OracleCircuit UnitaryGates (supArity ℓ t) N) (out : Qubits N → Idx ℓ),
          (∀ W ∈ G ℓ, ∀ orc, IsPAccess t W orc →
            tv (qOut alg orc out) (lenSqDist (padVec dec3 (gVec g t W))) ≤ ε) →
          c * Real.sqrt ((4 : ℝ) ^ ℓ) ≤ totalQueries alg) := by sorry

end QuarticGap.Supplement
