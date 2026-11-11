-- Prove2me | Theorems.Thm_RandModSubsetSum_theorem_3_2
-- name    : RandModSubsetSum.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:22.866362+00:00
-- url     : https://prove2.me/theorems/472f14e9-2efb-4eea-8be6-45aeebd292fd
-- title:
--   Theorem 3.2 — random integer subset sum with prescribed root counts (corrected: costs for $n\ge N(B)$)
-- statement:
--   There exist fixed stratum weights $w$ and parameters $\Theta$ (here: the paper's weights $w_r=W_r/10^{20}$ and two programs) such that the following holds. Fix $B>\delta_0$ and an integer $Q$ with $\delta_0n\le\log_2Q\le Bn$, and a root $x$ nearly balanced in every stratum, $|h_r-n_r/2|\le10^{-10}n_r$. Let $a$ be uniform in $\{0,\dots,Q-1\}^n$, $t=a\cdot x$ over the integers and $h=(h_r)_r$; the input is $(Q,a,t,h)$.
--
--   1. **Mode first** halts on every input and coin tape and returns FAIL or a solution $y\in\{0,1\}^n$ of $\sum_ka_ky_k=t$, $\sum_{k\in I_r}y_k=h_r$.
--   2. **Mode all** halts, and every word it emits is such a solution.
--   3. There are $c>0$ and $N$, depending on $B$, such that for $n\ge N$: every run of either mode uses at most $2^{0.261395n}$ bit operations and $2^{0.23728n}$ bits; $\Pr(\text{mode first returns FAIL})\le2^{-cn}$; and $\Pr(\text{mode all does not output }x\text{ before stopping})\le2^{-cn}$, the probabilities over the coefficients and the coins.
--
--   This is the integer search at the heart of the algorithm; Theorems 7.1 and 7.2 reduce the modular problem to it.
--
--   **Formalization Note** The machine is `TwMSOCount.Main` (bit time, bit space including input cells, fair coins). Mode all "outputs" a word when its program counter is at a fixed index $e$; the emitted word is the machine's output word at that step; emissions are not stored. Probabilities are $Q^{-n}\sum_a\mathrm{coinTape}(\cdot)$.
--
--   Differences from the source:
--   - generalization: there exist fixed stratum weights w → the paper's weights w_r = W_r/10²⁰ (Table 4); reason: a statement for the named weights implies the existence; it lets Theorem 7.1 use the same strata
--   - reading: nominal parameters Θ and RepresentationSearch (Algorithm 1) in modes first and all → two programs Pfirst and Pall of TwMSOCount.Main, chosen before B; reason: the procedure is abstracted to the existence of programs with its stated properties
--   - reading: mode all outputs the fixed root x before stopping → before the first halt, at some step with program counter e, the output word is x; every word at pc = e is a verified solution; reason: emission point of a streaming procedure on a RAM that halts once
--   - correction: in either mode, every run uses at most 2^{0.261395n} bit operations and 2^{0.23728n} bits (all n) → these cost bounds for n ≥ N(B); halting and validity for every n ≥ 1; reason: with space counted including input the bound is false for small n: n = 9060 (all strata even), x with n_r/2 ones per stratum, B = 2^{2200}, Q = 2^{2^{2160}} satisfy every assumption, yet Q alone occupies 2^{2160} + 1 > 2^{0.23728·9060} bits
--   - encoding: 2^{−Ω_B(n)}, for sufficiently large n depending on B; Pr over a and the coins → ∃ c > 0, ∃ N after B; Σ_a coinTape(event) ≤ 2^{−cn} Qⁿ; reason: Lean convention; same content
--   - encoding: input (Q, (a, t, h)) and output y or FAIL → the word (Q, t, a₁, …, a_n, h₁, …, h₁₃); output y₁, …, y_n, FAIL the empty word; reason: machine words
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Theorem 3.2, pp. 18–19; Problem 3.1, pp. 16–17

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_RandModSubsetSum_Strata
import Definitions.Def_RandModSubsetSum_Problem

open MeasureTheory TwMSOCount.Main
open scoped BigOperators ENNReal

namespace RandModSubsetSum

/-- **Theorem 3.2** (random integer subset sum; corrected: costs for `n ≥ N(B)`). Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), Theorem 3.2,
pp. 18–19, for Problem 3.1, pp. 16–17.

There exist fixed stratum weights `w` and parameters `Θ` such that, for every `B > δ₀`, every
integer `Q` with `δ₀ n ≤ log₂ Q ≤ B n` and every root `x` nearly balanced in every stratum:
mode first returns a solution of Problem 3.1 (integer equation `Σ a_k y_k = t` and root counts
`h`) or FAIL; for sufficiently large `n` depending on `B`, `Pr(FAIL) ≤ 2^{−Ω_B(n)}`; mode all
outputs the fixed root `x` before stopping with probability `1 − 2^{−Ω_B(n)}`; both probabilities
over the uniform coefficients `a ∈ {0, …, Q − 1}ⁿ` and the coins; every run uses at most
`2^{0.261395 n}` bit operations and `2^{0.23728 n}` bits.

**Formalization Note.** The machine is the published randomized log-cost RAM `TwMSOCount.Main`
(bit time, bit space with input cells, fair coin tape). The weights are the paper's `w_r = W_r/10²⁰`
(Table 4), which gives the existence of `w`; the parameters `Θ` and RepresentationSearch
(Algorithm 1) are abstracted into the two programs `Pfirst` (mode first) and `Pall` (mode all).
Mode all emits a solution when its program counter is at the index `e`; the emitted word is the
machine's output word at that step; each emission is a verified solution and emissions are not
stored. The input word is `(Q, t, a_1, …, a_n, h_1, …, h_13)` with `t = a · x` over the integers.
`2^{−Ω_B(n)}` and "sufficiently large `n` depending on `B`" are `∃ c > 0, ∃ N` after `B`. The
probability `Pr` is `Q^{−n} Σ_a coinTape(·)`, written without division. Validity and halting are
claimed for all `n ≥ 1`; the cost clause for `n ≥ N` (correction: with input-inclusive space it is
false for small `n`, e.g. `n = 9060`, `B = 2^{2200}`, `Q = 2^{2^{2160}}`). -/
theorem theorem_3_2 :
    ∃ (Pfirst Pall : Program) (e : ℕ), ∀ B : ℝ, delta0 < B →
      (∀ n : ℕ, 1 ≤ n → ∀ Q : ℕ, InRange B n Q → ∀ x : Fin n → Fin 2, NearBalanced paperWeight x →
        ∀ (a : Fin n → Fin Q) (τ : ℕ → Bool),
          (∃ s, runStats Pfirst τ (Config.init (intInput a (intTarget a x) (rootCount paperWeight x))) =
              some s ∧
            FailOrIntSolution paperWeight a (intTarget a x) (rootCount paperWeight x) s.final.output) ∧
          (∃ s, runStats Pall τ (Config.init (intInput a (intTarget a x) (rootCount paperWeight x))) =
              some s) ∧
          (∀ T : ℕ,
            (∀ T' ≤ T, ¬ halted Pall
              (run Pall τ (Config.init (intInput a (intTarget a x) (rootCount paperWeight x))) T')) →
            (run Pall τ (Config.init (intInput a (intTarget a x) (rootCount paperWeight x))) T).pc = e →
            ∃ y, IsIntSolution paperWeight a (intTarget a x) (rootCount paperWeight x) y ∧
              (run Pall τ (Config.init (intInput a (intTarget a x) (rootCount paperWeight x))) T).output =
                encSol y)) ∧
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ Q : ℕ, InRange B n Q →
        ∀ x : Fin n → Fin 2, NearBalanced paperWeight x →
          (∀ (a : Fin n → Fin Q) (τ : ℕ → Bool),
            (∃ s, runStats Pfirst τ (Config.init (intInput a (intTarget a x) (rootCount paperWeight x))) =
                some s ∧
              (s.time : ℝ) ≤ (2 : ℝ) ^ ((261395 / 10 ^ 6 : ℝ) * n) ∧
              (s.space : ℝ) ≤ (2 : ℝ) ^ ((23728 / 10 ^ 5 : ℝ) * n)) ∧
            (∃ s, runStats Pall τ (Config.init (intInput a (intTarget a x) (rootCount paperWeight x))) =
                some s ∧
              (s.time : ℝ) ≤ (2 : ℝ) ^ ((261395 / 10 ^ 6 : ℝ) * n) ∧
              (s.space : ℝ) ≤ (2 : ℝ) ^ ((23728 / 10 ^ 5 : ℝ) * n))) ∧
          (∑ a : Fin n → Fin Q, coinTape {τ | callOutput Pfirst
              (Config.init (intInput a (intTarget a x) (rootCount paperWeight x))) τ = some []}) ≤
            ENNReal.ofReal ((2 : ℝ) ^ (-c * n)) * (Q : ℝ≥0∞) ^ n ∧
          (∑ a : Fin n → Fin Q, coinTape {τ | ¬ ∃ T : ℕ,
              (∀ T' ≤ T, ¬ halted Pall
                (run Pall τ (Config.init (intInput a (intTarget a x) (rootCount paperWeight x))) T')) ∧
              (run Pall τ (Config.init (intInput a (intTarget a x) (rootCount paperWeight x))) T).pc = e ∧
              (run Pall τ (Config.init (intInput a (intTarget a x) (rootCount paperWeight x))) T).output =
                encSol x}) ≤
            ENNReal.ofReal ((2 : ℝ) ^ (-c * n)) * (Q : ℝ≥0∞) ^ n := by sorry

end RandModSubsetSum
