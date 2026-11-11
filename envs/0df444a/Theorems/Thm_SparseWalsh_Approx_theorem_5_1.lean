-- Prove2me | Theorems.Thm_SparseWalsh_Approx_theorem_5_1
-- name    : SparseWalsh.Approx.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:03:12.502881+00:00
-- url     : https://prove2.me/theorems/9c4830af-ceea-4301-bb5c-6c83df1a345b
-- title:
--   Theorem 5.1 — relative-error approximation tradeoffs: (1+ε)·OPT_s with probability 3/4 from non-adaptive value queries, four implementations
-- statement:
--   Let $f:\mathbb F_2^d\to\mathbb R$ be accessible only through exact value queries, and let $\mathrm{OPT}_s(f)=\min_{|\operatorname{supp}\hat g|\le s}\|f-g\|_2^2$ be the best $s$-term error under the uniform distribution. Theorem 5.1 gives four implementations of Algorithm 3: either method (repetition or coding) with either output limit ($s$ or $2s$ terms).
--
--   Formally, there are one admissible program $P$ of the machine of §2 and one universal constant $C$ with the following property. The program takes as input $d$, $s$, $\varepsilon$, the method flag, the output flag and $k$, where $k=0$ selects the general setting. Take any $d\ge1$, $1\le s\le2^d$, $0<\varepsilon\le1$, either method and either output limit $j\in\{s,2s\}$, and any $f$. The setting is either the general one, with $L=d$, or the degree setting, with $1\le k\le d$, some best $s$-term approximation of $f$ of degree at most $k$, and $L=k\log_2(2d/k)$. Put $\Lambda=\log_2(4ds/\varepsilon)$. Then:
--   - on every coin tape the run halts with work at most $C\,T_{\rm row}\,\Lambda^C$;
--   - every halted run has made at most $C\,Q_{\rm row}$ value queries;
--   - **non-adaptivity**: on a fixed tape, the query log is the same for every other oracle $f'$;
--   - every halted run either aborts or lists at most $j$ terms, with distinct frequencies and nonzero coefficients, all of weight at most $k$ in the degree setting;
--   - the run aborts, or its output $h$ violates
--   $$\|f-h\|_2^2\le(1+\varepsilon)\,\mathrm{OPT}_s(f),\qquad(2)$$
--   with probability at most $1/4$.
--
--   The rows of table (7), with $\log=\log_2$:
--
--   | method | output terms | $Q_{\rm row}$ | $T_{\rm row}$ |
--   |---|---|---|---|
--   | repetition | $\le s$ | $sL\log(2L)/\varepsilon+(s/\varepsilon^2)\log(2s/\varepsilon)$ | $ds/\varepsilon^2$ |
--   | repetition | $\le 2s$ | $sL\log(2L)/\varepsilon+(s/\varepsilon)\log(2s/\varepsilon)$ | $ds/\varepsilon$ |
--   | coding | $\le s$ | $sL/\varepsilon+(s/\varepsilon^2)\log(2s/\varepsilon)$ | $dLs/\varepsilon+ds/\varepsilon^2$ |
--   | coding | $\le 2s$ | $sL/\varepsilon+(s/\varepsilon)\log(2s/\varepsilon)$ | $dLs/\varepsilon$ |
--
--   This is the paper's main result on relative-error approximation. It gives a $(1+\varepsilon)$-approximation to the best $s$-term Fourier approximation from non-adaptive queries in near-linear time. With at most $2s$ output terms the dependence on $\varepsilon$ improves from $1/\varepsilon^2$ to $1/\varepsilon$, against the same best-$s$-term benchmark.
--
--   Differences from the source:
--
--   - reading: Algorithm 3 has four implementations → one admissible program with the method and output flags (and k) as inputs, chosen with one universal C before the instance; reason: one program covering all four rows and both settings is at least as strong as four programs
--   - reading: the computational model of §2 (unit-cost real arithmetic, binary data in bit operations, unit-cost memory access, unit oracle overhead) → the machine SparseWalsh.Approx.Machine: the SmaleNinth real-RAM core with a ZMod 2 bit bank, fair coins and a value query with a query log; cost 1 per instruction plus the bit lengths of integer operands and addresses; reason: makes "a frequency is not treated as one machine word" precise; logarithmic address cost differs from unit-cost access by logarithmic factors, which the Õ absorbs
--   - encoding: Queries O(·); Total time Õ(·) → queries ≤ C·Q_row; work ≤ C·T_row·Λ^C with Λ = log₂(4ds/ε); log = log₂; reason: Õ suppresses logarithmic factors in d, s, 1/ε (Table 1 caption), each at most a power of Λ ≥ 2
--   - reading: worst-case total running times; query counts → on every coin tape the run halts within the time bound, and every halted run has made at most C·Q_row queries; reason: §2: "The stated running-time bounds hold on every execution"
--   - reading: uses non-adaptive value queries → on every tape the query log at halt is the same for every oracle f′; reason: all query points are determined by the inputs and the internal randomness before any answer is observed (p. 11)
--   - encoding: satisfying (2) with probability at least 3/4 (a timeout returns failure) → the coin-tape measure of the set of tapes on which the run aborts or violates (2) is at most 1/4; reason: Lean measures non-measurable sets by outer measure; §2 counts a timeout as failure
--   - reading: L = O(k log(2d/k)) under the degree promise, with all output frequencies of weight at most k → L = k·log₂(2d/k) inside C·(…); k = 0 encodes the general setting (L = d); in the degree setting every listed frequency has weight ≤ k on every non-aborted run; reason: the O-constant is absorbed into C
--   - encoding: the output lists the nonzero coefficients of h and their frequencies; at most j terms → memory output list: at most j entries, pairwise distinct frequencies, nonzero coefficients; h = Σ coeff·χ_freq; reason: Definition 2.3, p. 12
--   - encoding: min_{|supp ĝ| ≤ s} ‖f − g‖₂² → bestErr s f, the infimum of the attained values (a minimum, p. 11); reason: equal values
-- source:
--   Attias, Bshouty, Medvedev, Srebro, Efficient Non-Adaptive Sparse Fourier Learning on the Boolean Cube and Finite Abelian Groups, STOC 2027 submission (manuscript sha256 4cbf9075…), p. 19 (PDF p. 22), Theorem 5.1 and table (7); p. 20 (PDF p. 23), the paragraph on L; Eq. (2), Definition 2.3, p. 12

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_SparseWalsh_Approx_Fourier
import Definitions.Def_SparseWalsh_Approx_Machine

open scoped BigOperators Matrix

namespace SparseWalsh.Approx

/-- **Theorem 5.1** (Relative-error approximation tradeoffs), p. 19 (PDF p. 22); the paragraph
on `L` is on p. 20 (PDF p. 23).

"Algorithm 3 has four implementations" is read as one admissible program `P` of the machine
`SparseWalsh.Approx` (inputs `d, s, ε`, the method flag `coding`, the output flag `twoS`: `j = s`
or `j = 2s`, and `k`, with `k = 0` the general setting), chosen together with one universal
constant `C` before the instance. For every `d ≥ 1`, `1 ≤ s ≤ 2^d`, `ε ∈ (0, 1]`, both methods,
both output limits and every `f : F_2^d → ℝ` — in the general setting (`L = d`), and in the degree
setting (`1 ≤ k ≤ d` and some best `s`-term approximation of `f` has degree `≤ k`;
`L = k·log₂(2d/k)`):
* on every coin tape the run halts with `work ≤ C·T_row·Λ^C`, `Λ = log₂(4ds/ε)`;
* every halted run has made at most `C·Q_row` value queries;
* non-adaptivity: on a fixed tape, the query log at halt is the same for every oracle `f'`;
* every halted run either aborts or lists at most `j` terms with distinct frequencies and nonzero
  coefficients, all of weight `≤ k` in the degree setting;
* the set of tapes on which the run aborts or its output `h` violates
  `‖f − h‖₂² ≤ (1 + ε)·min_{|supp ĝ| ≤ s} ‖f − g‖₂²` (Eq. (2)) has probability at most `1/4`.
Rows of (7), `log = log₂`: repetition/`≤ s`: `Q = sL log(2L)/ε + (s/ε²)log(2s/ε)`, `T = ds/ε²`;
repetition/`≤ 2s`: `Q = sL log(2L)/ε + (s/ε)log(2s/ε)`, `T = ds/ε`; coding/`≤ s`:
`Q = sL/ε + (s/ε²)log(2s/ε)`, `T = dLs/ε + ds/ε²`; coding/`≤ 2s`: `Q = sL/ε + (s/ε)log(2s/ε)`,
`T = dLs/ε`. -/
theorem theorem_5_1 :
    ∃ (P : Program) (_ : Admissible P) (C : ℝ), 0 < C ∧
      ∀ d s : ℕ, 1 ≤ d → 1 ≤ s → s ≤ 2 ^ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (coding twoS : Bool) (k : ℕ), (k = 0 ∨ (1 ≤ k ∧ k ≤ d)) →
      ∀ f : Cube d → ℝ, (k ≠ 0 → DegreePromise s k f) →
        let j : ℕ := if twoS then 2 * s else s
        let L : ℝ := if k = 0 then (d : ℝ) else k * Real.logb 2 (2 * d / k)
        let Λ : ℝ := Real.logb 2 (4 * d * s / ε)
        let Qrow : ℝ :=
          (if coding then s * L / ε else s * L * Real.logb 2 (2 * L) / ε) +
            (if twoS then s / ε else s / ε ^ 2) * Real.logb 2 (2 * s / ε)
        let Trow : ℝ :=
          if coding then (if twoS then d * L * s / ε else d * L * s / ε + d * s / ε ^ 2)
          else (if twoS then d * s / ε else d * s / ε ^ 2)
        let s₀ := approxInit d s ε coding twoS k
        (∀ ω : ℕ → Bool, ∃ n : ℕ, (run P f s₀ ω n).halted = true ∧
          ((run P f s₀ ω n).work : ℝ) ≤ C * Trow * Λ ^ C) ∧
        (∀ (ω : ℕ → Bool) (n : ℕ), (run P f s₀ ω n).halted = true →
          ((run P f s₀ ω n).queries : ℝ) ≤ C * Qrow) ∧
        (∀ (f' : Cube d → ℝ) (ω : ℕ → Bool) (n n' : ℕ), (run P f s₀ ω n).halted = true →
          (run P f' s₀ ω n').halted = true →
          (run P f s₀ ω n).queryLog = (run P f' s₀ ω n').queryLog) ∧
        (∀ (ω : ℕ → Bool) (n : ℕ), (run P f s₀ ω n).halted = true →
          aborted (run P f s₀ ω n) ∨
            (outLength (run P f s₀ ω n) ≤ j ∧
              ((outList (run P f s₀ ω n)).map Prod.fst).Nodup ∧
              (∀ e ∈ outList (run P f s₀ ω n), e.2 ≠ 0) ∧
              (k ≠ 0 → ∀ e ∈ outList (run P f s₀ ω n), weight e.1 ≤ k))) ∧
        coinTape {ω | ∃ n : ℕ, (run P f s₀ ω n).halted = true ∧
          (aborted (run P f s₀ ω n) ∨
            ¬ normSq (f - outPoly (run P f s₀ ω n)) ≤ (1 + ε) * bestErr s f)} ≤ 1 / 4 := by sorry

end SparseWalsh.Approx
