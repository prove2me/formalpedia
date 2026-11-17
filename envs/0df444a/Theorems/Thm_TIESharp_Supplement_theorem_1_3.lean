-- Prove2me | Theorems.Thm_TIESharp_Supplement_theorem_1_3
-- name    : TIESharp.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:57:27.547889+00:00
-- url     : https://prove2.me/theorems/ba09e1a4-ec4c-48c9-af68-b0b98a7c6a32
-- title:
--   Theorem 1.3 — one TIE mechanism attains the ratios of Theorems 1.1–1.2 for every $n\ge4$ in expected polynomial bit time, with rational payments covering reported cost
-- statement:
--   Let $R(n)$ be $(n+1)/2$ for $n\ge7$ and $3$, $105/32$, $29/8$ for $n=4,5,6$ (the upper bounds of Theorems 1.1 and 1.2). There exist a mechanism family $F_n$ on $n$ machines for every $n$, a single program $P$ of the log-cost rational RAM with fair coins, and constants $C,K\in\mathbb N$ such that for every $n\ge4$:
--
--   1. $F_n$ is feasible (every assignment law is a probability distribution), truthful in expectation, and $R(n)$-approximate: at truthful reports its expected makespan is at most $R(n)\,\mathrm{OPT}(t)$ for every number of jobs $m\ge0$ and every nonnegative real processing-time matrix $t$;
--   2. for every $m\ge0$ and every nonnegative rational report matrix $b\in\mathbb Q_{\ge0}^{n\times m}$, run on the binary input $\langle n,m,b\rangle$ (the number of jobs, then the $n$ report rows, each opened by a marker bit) with independent fair coins:
--      - the run halts with probability one;
--      - every halting run outputs the code of an assignment $A$ and rational payments $\pi$ with $\pi_i\ge0$ and $\pi_i\ge L_i(b,A)=\sum_{j:A(j)=i}b_{ij}$ for every machine $i$;
--      - the sampled assignment is distributed as $F_n$'s assignment law at $b$, and each machine's realized payment has expectation equal to $F_n$'s expected payment $p_i(b)$;
--      - the expected number of bit operations satisfies
--      $$\mathbb E\big[\mathrm{cost}_P(\langle n,m,b\rangle)\big]\le C\,\big(|\langle n,m,b\rangle|+1\big)^K .$$
--
--   So one efficiently implementable mechanism attains the ratios of Theorems 1.1 and 1.2 for every $n\ge4$, with exact rational outputs, polynomial expected bit time even when $n$ is part of the input, and payments that cover each machine's reported load in every outcome.
--
--   **Formalization Note** The machine is the published `BlottoFPTAS.Main.BitRAM`. Payments are gross payments, as in the utility $p_i-\sum_j t_{ij}q_{ij}$ of `TIESharp.IsTIE`. The realized payment is read from the decoded output and is $0$ on the null set of tapes whose output does not decode.
--
--   Differences from the source:
--   - reading: "A single truthful-in-expectation mechanism … for every n ≥ 4" (n part of the input) → a family F n for each n together with one program P and constants C, K, all chosen before n; reason: the mechanism receives n as input, so one program serves every n; its real-valued law at n is F n
--   - reading: no machine named; "unbiased random bits", "expected running time … total binary input length" → the published log-cost rational RAM BlottoFPTAS.Main.BitRAM with its fair-coin tape coinTape and bit cost bitCostE (⊤ on a non-halting run); reason: the paper fixes no machine; polynomial expected bit time is robust across reasonable bit models
--   - reading: expected running time polynomial in the total binary input length, even when n is part of the input → ∫⁻ bitCostE ≤ C·(|input| + 1)^K with C, K independent of n, m and b; reason: every polynomial in L is at most C(L+1)^K, and C, K may not depend on n
--   - encoding: rational reports and sampled outcome (no format given) → input inputCode n m b (m, then the n report rows, each opened by a marker bit, so n is the number of rows); output outputCode A π, read back with decodeOutcome; reason: the paper names no format; every machine contributes at least one input bit, as in any listing of an n × m matrix, so the n payments of an outcome (even at m = 0) can be written in time polynomial in the input length
--   - reading: "uses unbiased random bits to sample an assignment and nonnegative rational payments" implementing the mechanism → the run halts almost surely; the decoded assignment has law (F n).alloc m b; each realized payment is integrable with mean (F n).pay m b i; reason: this is what implementing the TIE mechanism means (proof, p.31: Proposition 6.1 samples the assignment, Lemma 6.2 realizes the expected payments)
--   - reading: "In every outcome each machine's payment covers its reported processing cost" → on every halting coin tape the output decodes to (A, π) with 0 ≤ π_i and L_i(b, A) = Σ_{j : A j = i} b_ij ≤ π_i; reason: proof, p.31: "b̂P_i ≥ L_i(b, A) in every outcome"; every outcome = every halting run, not only almost every
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134, Theorem 1.3, p.2 (PDF p.3); proof §6, pp.29–31 (PDF pp.30–32), proof of Theorem 1.3 p.31

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_TIESharp_IsFeasible
import Definitions.Def_TIESharp_IsTIE
import Definitions.Def_TIESharp_IsRApprox
import Definitions.Def_BlottoFPTAS_Main_BitRAM
import Definitions.Def_TIESharp_Supplement_ratioBound
import Definitions.Def_TIESharp_Supplement_inputCode
import Definitions.Def_TIESharp_Supplement_decodeOutcome

set_option autoImplicit false

open MeasureTheory

namespace TIESharp

namespace Supplement

open BlottoFPTAS.Main.BitRAM

/-- **Theorem 1.3 (Efficient implementation)** (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, Theorem 1.3, p.2; proof §6, pp.29–31). A single
truthful-in-expectation mechanism gives the upper bounds of Theorems 1.1 and 1.2 for every
`n ≥ 4`. On nonnegative rational reports it uses unbiased random bits to sample an assignment and
nonnegative rational payments. Its expected running time is polynomial in the total binary input
length, even when `n` is part of the input. In every outcome each machine's payment covers its
reported processing cost.

There are a mechanism family `F n` for every `n`, one program `P` of the log-cost rational RAM
and constants `C, K` (all chosen before `n`) such that for every `n ≥ 4`:
* `F n` is feasible, truthful in expectation, and `ratioBound n`-approximate over all
  nonnegative real profiles (`ratioBound n = (n+1)/2` for `n ≥ 7`, `3, 105/32, 29/8` for
  `n = 4, 5, 6`);
* for every `m` and every nonnegative rational report `b`, with input `inputCode n m b`:
  (a) the run halts with probability one over the fair coins; (b) every halting run outputs the
  code of an assignment `A` and payments `π` with `π_i ≥ 0` and `π_i ≥ L_i(b, A)` (reported
  load); (c) the sampled assignment has law `(F n).alloc m b`; (d) each machine's realized
  payment is integrable with mean `(F n).pay m b i`; (e) the expected bit cost is at most
  `C · (|input| + 1)^K`.

**Formalization Note.** The machine is the published `BlottoFPTAS.Main.BitRAM` (log-cost
rational RAM, fair-coin tape `coinTape`, bit cost `bitCostE`, `⊤` on a non-halting run). Payments
are gross payments, as in `TIESharp.IsTIE`. The realized payment is read from the decoded output,
and is `0` on the (null) set of tapes whose output does not decode. -/
theorem theorem_1_3 :
    ∃ (F : (n : ℕ) → Family n) (P : Program) (C K : ℕ),
      ∀ n : ℕ, 4 ≤ n →
        IsFeasible (F n) ∧ IsTIE (F n) ∧ IsRApprox (F n) (ratioBound n) ∧
        ∀ (m : ℕ) (b : Fin n → Fin m → ℚ), (∀ i j, 0 ≤ b i j) →
          (∀ᵐ ω ∂coinTape, Halts P (inputCode n m b) ω) ∧
          (∀ ω, Halts P (inputCode n m b) ω →
            ∃ (A : Fin m → Fin n) (π : Fin n → ℚ),
              decodeOutcome n m (output P (inputCode n m b) ω) = some (A, π) ∧
              ∀ i, 0 ≤ π i ∧
                MatousekLP.Scheduling.load (Matrix.of fun i j => (b i j : ℝ)) A i ≤ (π i : ℝ)) ∧
          (∀ A₀ : Fin m → Fin n,
            coinTape {ω | (decodeOutcome n m (output P (inputCode n m b) ω)).map Prod.fst
                = some A₀} =
              ENNReal.ofReal ((F n).alloc m (fun i j => (b i j : ℝ)) A₀)) ∧
          (∀ i : Fin n,
            Integrable (fun ω => (decodeOutcome n m (output P (inputCode n m b) ω)).elim
              (0 : ℝ) fun o => (o.2 i : ℝ)) coinTape ∧
            ∫ ω, (decodeOutcome n m (output P (inputCode n m b) ω)).elim
                (0 : ℝ) (fun o => (o.2 i : ℝ)) ∂coinTape =
              (F n).pay m (fun i j => (b i j : ℝ)) i) ∧
          ∫⁻ ω, bitCostE P (inputCode n m b) ω ∂coinTape ≤
            (C : ENNReal) * (((inputCode n m b).length : ENNReal) + 1) ^ K := by sorry

end Supplement

end TIESharp
