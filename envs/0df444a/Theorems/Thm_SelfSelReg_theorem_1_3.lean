-- Prove2me | Theorems.Thm_SelfSelReg_theorem_1_3
-- name    : SelfSelReg.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:59.243342+00:00
-- url     : https://prove2.me/theorems/5882fb64-706f-49f1-97b7-7f6f8b4fa8e1
-- title:
--   Theorem 1.3 — polynomial-time self-selection: all $k$ regressors to error $\varepsilon$ w.p. $1-\delta$ from $\widetilde O((nk/\varepsilon)^{\mathrm{poly}(B/\Delta)}\log(1/\delta))$ samples and time
-- statement:
--   In the Gaussian maximum self-selection model one observes i.i.d. pairs $(X,Y_{\max})$ with $X\sim N(0,I_n)$, $Y_{\max}=\max_{i\in[k]}(\langle w_i,X\rangle+\xi_i)$ and $\xi_i$ i.i.d. $N(0,1)$ independent of $X$; the maximizing index is not observed. The unknown regressors satisfy Assumption 1.2: $\Delta\le\|w_i\|_2\le B$ and $|\langle w_i,w_j\rangle|\le\min\{\|w_i\|_2^2,\|w_j\|_2^2\}-\Delta^2$ for $i\ne j$, with $B\ge1$ and $\Delta\in(0,1]$.
--
--   **Theorem.** There is a randomized algorithm and a constant such that, for all $n,k$ with $2\le k\le n$, all $\varepsilon\in(0,1)$, $\delta\in(0,1/3)$, $B\ge1$, $\Delta\in(0,1]$ and all regressors satisfying Assumption 1.2, the algorithm, given $k,\varepsilon,\delta,B,\Delta$ and sample access to the model, returns $\hat w_1,\dots,\hat w_k\in\mathbb R^n$ such that with probability at least $1-\delta$ there is a permutation $\pi$ of $[k]$ with
--   $$\max_{i\in[k]}\|\hat w_i-w_{\pi(i)}\|_2\le\varepsilon,$$
--   and its sample complexity and running time are both
--   $$\widetilde O\Big(\Big(\frac{nk}{\varepsilon}\Big)^{\mathrm{poly}(B/\Delta)}\log\frac1\delta\Big).$$
--
--   This is the first algorithm for the self-selection problem with sample complexity and running time polynomial in $n$, $k$ and $1/\varepsilon$ for fixed $B/\Delta$; earlier algorithms were exponential in $k$ in time.
--
--   **Formalization Note** The algorithm is one program of the published sampling real RAM `GaussMixHH`, restricted to exact arithmetic, comparisons, pointer moves, fair coins, `sample` and `halt` (`ArithmeticCoin`), chosen together with one constant $C\in\mathbb N$ before every parameter and every instance. It reads $k,\varepsilon,\delta,B,\Delta$ from memory, runs in dimension $n+1$ (one observation per `sample`, cost $n+1$), and writes the $k$ vectors to memory (`decodeOutput`). On every coin tape and sample stream it halts with at most $C(nk/\varepsilon)^{C(B/\Delta)^C}\log(1/\delta)$ samples and work; and on a measurable set of runs of probability at least $1-\delta$ every halted state has a permutation $\pi$ with $\|\hat w_i-w_{\pi(i)}\|_2\le\varepsilon$ for all $i$.
--
--   Differences from the source:
--   - reading: "a randomized algorithm" whose running time counts "operations", with no machine named → one Admissible, ArithmeticCoin program of the GaussMixHH sampling real RAM (exact + − × ÷, rational literals, comparisons, pointer moves, fair coins, sample, halt), the same for every input; work counts executed instructions, sample costs n + 1; reason: the non-weaker reading: any further unit-cost primitive (√, exp, an eigensolver, Φ) would weaken the theorem
--   - reading: Õ((nk/ε)^{poly(B/∆)} log(1/δ)) → C · (nk/ε)^{C·(B/∆)^C} · log(1/δ) for one C ∈ ℕ chosen with the program; reason: Õ suppresses logarithms in n, k, 1/ε (Proposition G.1), absorbed by the exponent since nk/ε ≥ 4; poly(K) = poly(B/∆) since K ≤ 128(B/∆)^{10}; no log log(1/δ) factor is admitted (the stronger reading)
--   - reading: sample complexity and running time → worst-case bounds on samples and on work, on every coin tape and sample stream; reason: the non-weaker reading; Algorithm 9.1 makes at most 2k calls with deterministic sample counts
--   - reading: B and ∆ "absolute constants" of Assumption 1.2 → inputs of the program, quantified after the program and C; reason: Algorithm 9.1 takes them as input ("Known B, ∆, k, ε, δ"); one program and one constant for all B, ∆ is the uniform, stronger reading
--   - encoding: "with probability at least 1 − δ … there is a permutation π … max_i ‖ŵ_i − w_{π(i)}‖₂ ≤ ε" → a measurable set E of runs with 1 − δ ≤ P(E) on which every halted state has π with ‖ŵ_i − w_{π(i)}‖ ≤ ε for all i; reason: avoids outer measure; same event for a halting program
--   - encoding: sample access to (X, Y_max), inputs k, ε, δ, B, ∆, output ŵ_1, …, ŵ_k → one observation as a vector of ℝ^{n+1} with Y_max last; input list [k, ε, δ, B, ∆] and n + 1 in pointer 0; output cell p[1] + i·n + j for coordinate j of ŵ_i; reason: the page fixes no formats
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Theorem 1.3, p.2–3 (PDF pp.5–6); proof §9, Algorithm 9.1, pp.66–67 (PDF pp.69–70); Proposition G.1, pp.94–95 (PDF pp.97–98)

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_SelfSelReg_SatisfiesAssumption
import Definitions.Def_SelfSelReg_sampleLaw
import Definitions.Def_SelfSelReg_ArithmeticCoin
import Definitions.Def_SelfSelReg_goalInput

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- **Theorem 1.3** (Polynomial-Time Self-Selection).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Theorem 1.3, p.2–3 (PDF pp.5–6); proof §9, pp.66–67 (PDF pp.69–70):
"There is a randomized algorithm with the following guarantee. Given k ≥ 2, desired error ε ∈ (0, 1),
failure probability δ ∈ (0, 1/3), and sample access to an instance of the self-selection model
(Definition 1.1) satisfying boundedness and uncoveredness conditions (Assumption 1.2) with constants
∆, B, the algorithm returns ŵ_1, …, ŵ_k ∈ ℝⁿ such that, with probability at least 1 − δ, there is a
permutation π of the indices under which max_i ‖ŵ_i − w_{π(i)}‖₂ ≤ ε. Its sample complexity and
running time are both Õ((nk/ε)^{poly(B/∆)} log(1/δ))."

**Formalization Note.**
* The algorithm is one program `P` of the published sampling real RAM `GaussMixHH`, restricted by
  `ArithmeticCoin` to exact `+ − × ÷`, rational literals, comparisons, memory and pointer moves, fair
  coins, `sample` and `halt` (no `√`, `exp`, `cos`, `sin`). `P` and the constant `C` are chosen before
  every parameter and every instance. `P` runs in dimension `n + 1`, receives `k, ε, δ, B, ∆` in
  memory (`goalInput`) and `n + 1` in pointer `0`, and reaches the instance only through `sample`,
  which writes one observation `(X, Y_max)` (cost `n + 1`).
* `Õ(·)` and `poly(B/∆)`: one natural number `C`, and the bound
  `C · (nk/ε)^{C·(B/∆)^C} · log(1/δ)` (`resourceBound`) on the number of samples **and** on the work,
  on **every** coin tape and sample stream.
* The output is `k` vectors of `ℝⁿ` decoded from memory (`decodeOutput`). "With probability at least
  `1 − δ`": a measurable set of runs of `sampleSpace w`-measure at least `1 − δ` on which every halted
  state admits a permutation `π` with `‖ŵ_i − w_{π(i)}‖₂ ≤ ε` for all `i`.
* `n, k` satisfy `2 ≤ k ≤ n` (Definition 1.1); `B ≥ 1`, `∆ ∈ (0, 1]` (Assumption 1.2). -/
theorem theorem_1_3 :
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticCoin P) (C : ℕ),
      ∀ (n k : ℕ), 2 ≤ k → k ≤ n →
      ∀ (ε δ B Δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 / 3 → 1 ≤ B → 0 < Δ → Δ ≤ 1 →
      ∀ w : Fin k → EuclideanSpace ℝ (Fin n), SatisfiesAssumption B Δ w →
        (∀ ω : (ℕ → Bool) × (ℕ → EuclideanSpace ℝ (Fin (n + 1))), ∃ t : ℕ,
          (GaussMixHH.run P (n + 1) (GaussMixHH.initState (n + 1) (goalInput k ε δ B Δ)) ω t).halted
              = true ∧
          ((GaussMixHH.run P (n + 1) (GaussMixHH.initState (n + 1) (goalInput k ε δ B Δ)) ω
              t).samplesUsed : ℝ) ≤ resourceBound C n k ε δ B Δ ∧
          ((GaussMixHH.run P (n + 1) (GaussMixHH.initState (n + 1) (goalInput k ε δ B Δ)) ω
              t).work : ℝ) ≤ resourceBound C n k ε δ B Δ) ∧
        ∃ E : Set ((ℕ → Bool) × (ℕ → EuclideanSpace ℝ (Fin (n + 1)))), MeasurableSet E ∧
          ENNReal.ofReal (1 - δ) ≤ sampleSpace w E ∧
          ∀ ω ∈ E, ∀ t : ℕ,
            (GaussMixHH.run P (n + 1) (GaussMixHH.initState (n + 1) (goalInput k ε δ B Δ)) ω
              t).halted = true →
            ∃ π : Equiv.Perm (Fin k), ∀ i,
              ‖decodeOutput n k (GaussMixHH.run P (n + 1)
                  (GaussMixHH.initState (n + 1) (goalInput k ε δ B Δ)) ω t) i - w (π i)‖ ≤ ε := by sorry

end SelfSelReg
