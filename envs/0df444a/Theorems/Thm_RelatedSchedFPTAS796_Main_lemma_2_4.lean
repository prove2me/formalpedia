-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_lemma_2_4
-- name    : RelatedSchedFPTAS796.Main.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:14:32.132225+00:00
-- url     : https://prove2.me/theorems/febd5679-0abc-42d0-905d-392862a0bc81
-- title:
--   Lemma 2.4 ([BFN25]) (corrected: $\log(N+2)$, $\log(|A+B|+2)$) — output-sensitive sumsets in $[N]^d$
-- statement:
--   For fixed $d$, given nonempty $A,B\subseteq[N]^d$, one can compute $A+B$ in time
--
--   1. $O_d(|A+B|\cdot\mathrm{polylog}(N+2))$ by a deterministic algorithm, and
--   2. $O_d(|A+B|\cdot\log(|A+B|+2))$ by a Las Vegas algorithm.
--
--   Formally: for every $d$ there are (1) a coin-free word-RAM program and constants $b,C,c$ such that on every input (duplicate-free lists of points in any order) and at every width $w\ge b(\lfloor\log_2(L+M+2)\rfloor+1)$ it halts within $C\,|A+B|\,(\log_2(N+2))^c$ steps with output exactly $A+B$; and (2) a program and constants $b,C$ such that, at every such width, whenever the run halts its output is exactly $A+B$, and its expected halting time under the uniform law of the coins is at most $C\,|A+B|\log_2(|A+B|+2)$.
--
--   These are the convolution routines of Bringmann, Fischer and Nakos and of Jin and Xu, transferred to $[N]^d$ by the base-$(2N+1)$ encoding; Lemma 5.7 merges pairs of profile sets with the first one.
--
--   **Formalization Note** Logarithms are base 2. The halting time is the least number of steps after which the run has halted ($\infty$ if it never halts), and the expectation is its integral against the coin law.
--
--   Differences from the source:
--   - correction: $O_d(|A+B|\,\mathrm{polylog}\,N)$ and $O_d(|A+B|\log|A+B|)$ → $C|A+B|(\log_2(N+2))^c$ and $C|A+B|\log_2(|A+B|+2)$; reason: counterexample $A=B=\{0\}\subseteq[0]^d$: every assumption holds, $|A+B|=1$, the printed bounds are $0$ (or $\log 0$), but every run executes at least one instruction; the shift is the paper's own $\log(n+2)$ convention and changes nothing for large sizes
--   - reading: "the standard word RAM model" (p.7), no instruction set named → one program of the published randomized word RAM `MatroidSensOracle` (unit cost, $w$-bit words), required at every width $w\ge b(\lfloor\log_2(L+M+2)\rfloor+1)$ with $b$ fixed with the program; reason: the trans-dichotomous convention: every input number fits in $O(1)$ words and the width does not grow with the input length
--   - encoding: given $A,B\subseteq[N]^d$; compute $A+B$ → input $N,|A|,|B|$ and the points as duplicate-free lists in any order; output the count and the points of $A+B$ without repetition; reason: the paper fixes no representation of a set
--   - reading: a deterministic algorithm; a Las Vegas algorithm → a program without coin instructions; a program that is always correct when it halts, with a bound on its expected halting time; reason: the standard meanings of these words
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.8, Lemma 2.4 ([BFN25])

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM
import Definitions.Def_RelatedSchedFPTAS796_Main_Model
import Definitions.Def_RelatedSchedFPTAS796_Main_Machine
import Definitions.Def_RelatedSchedFPTAS796_Main_Problems

set_option autoImplicit false

open MatroidSensOracle MeasureTheory Pointwise

namespace RelatedSchedFPTAS796.Main

/-- **Lemma 2.4 ([BFN25])**, p.8, with the logarithms shifted to `log(N + 2)` and
`log(|A + B| + 2)` (the printed `polylog N` and `log |A + B|` vanish at `A = B = {0} ⊆ [0]^d`,
where no run can take `0` steps). For fixed `d`, given nonempty `A, B ⊆ [N]^d` (duplicate-free
lists of points in any order), one can compute `A + B`
1. in `O_d(|A + B| · polylog(N + 2))` time by a deterministic (coin-free) program: on every input
   and at every width `w ≥ b(⌊log₂(L + M + 2)⌋ + 1)` it halts within
   `C|A + B|(log₂(N + 2))^c` steps with output exactly `A + B`; and
2. in `O_d(|A + B| · log(|A + B| + 2))` time by a Las Vegas program: whenever it halts its output
   is exactly `A + B`, and its expected halting time is at most `C|A + B| log₂(|A + B| + 2)`. -/
theorem lemma_2_4 (d : ℕ) :
    (∃ (P : List Instr) (b C c : ℕ), CoinFree P ∧
      ∀ (N : ℕ) (A B : Finset (Fin d → ℕ)) (lA lB : List (Fin d → ℕ)),
        A.Nonempty → B.Nonempty → InCube N A → InCube N B → ListsSet lA A → ListsSet lB B →
        ∀ w : ℕ, widthMin b (sumsetInput N lA lB).length (maxWord (sumsetInput N lA lB)) ≤ w →
          ∀ ω : Coins, ∃ mem, runFor P w (sumsetInput N lA lB)
              (C * ((A + B).card : ℝ) * Real.logb 2 ((N : ℝ) + 2) ^ c) ω = some mem ∧
            OutputsNatSet mem (A + B)) ∧
    (∃ (P : List Instr) (b C : ℕ),
      ∀ (N : ℕ) (A B : Finset (Fin d → ℕ)) (lA lB : List (Fin d → ℕ)),
        A.Nonempty → B.Nonempty → InCube N A → InCube N B → ListsSet lA A → ListsSet lB B →
        ∀ w : ℕ, widthMin b (sumsetInput N lA lB).length (maxWord (sumsetInput N lA lB)) ≤ w →
          (∀ (ω : Coins) (t : ℕ) (mem : ℤ → BitVec w),
              exec P ω t 0 0 (loadWords w (sumsetInput N lA lB)) = some mem →
              OutputsNatSet mem (A + B)) ∧
          ∫⁻ ω, ((haltTime P w (sumsetInput N lA lB) ω : ℕ∞) : ENNReal) ∂coinLaw ≤
            ENNReal.ofReal (C * ((A + B).card : ℝ) * Real.logb 2 (((A + B).card : ℝ) + 2))) := by sorry

end RelatedSchedFPTAS796.Main
