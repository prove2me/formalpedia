-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_lemma_2_3
-- name    : RelatedSchedFPTAS796.Main.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:14:42.846847+00:00
-- url     : https://prove2.me/theorems/7ee2fed0-3f70-4fef-ba9b-3bf813762e97
-- title:
--   Lemma 2.3 — $A+B$ for $A,B\subseteq[N]^d$ in $O_d((N+1)^d\log(N+2))$ time
-- statement:
--   For fixed $d$ and an integer $N\ge0$, given $A,B\subseteq[N]^d$ (with $[N]=\{0,\dots,N\}$), one can compute the sumset $A+B$ in
--   $$O_d\big((N+1)^d\log(N+2)\big)$$
--   time. Formally: for every $d$ there are a word-RAM program and constants $b,C$ such that for all $N$ and all $A,B\subseteq[N]^d$, given as duplicate-free lists of points in any order, at every word width $w\ge b(\lfloor\log_2(L+M+2)\rfloor+1)$ ($L$ the number of input words, $M$ the largest one), on every coin sequence the program halts within $C(N+1)^d\log_2(N+2)$ steps and outputs exactly the set $A+B$, without repetition.
--
--   This is the FFT-based dense convolution, used in Lemma 2.5 and in the class combination of Lemmas 3.2 and 3.4.
--
--   Differences from the source:
--   - reading: "the standard word RAM model" (p.7), no instruction set named → one program of the published randomized word RAM `MatroidSensOracle` (unit cost, $w$-bit words), required at every width $w\ge b(\lfloor\log_2(L+M+2)\rfloor+1)$ with $b$ fixed with the program; reason: the trans-dichotomous convention: every input number fits in $O(1)$ words and the width does not grow with the input length
--   - encoding: given $A,B\subseteq[N]^d$; compute $A+B$ → input $N,|A|,|B|$ and the points as duplicate-free lists in any order; output the count and the points of $A+B$ without repetition; reason: the paper fixes no representation of a set
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.8, Lemma 2.3

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM
import Definitions.Def_RelatedSchedFPTAS796_Main_Model
import Definitions.Def_RelatedSchedFPTAS796_Main_Machine
import Definitions.Def_RelatedSchedFPTAS796_Main_Problems

set_option autoImplicit false

open MatroidSensOracle MeasureTheory Pointwise

namespace RelatedSchedFPTAS796.Main

/-- **Lemma 2.3**, p.8. For fixed `d` and an integer `N ≥ 0`, given `A, B ⊆ [N]^d`, one can compute
`A + B` in `O_d((N + 1)^d log(N + 2))` time. For every `d` there are a program and constants `b, C`
such that for all `N` and all `A, B ⊆ [N]^d` (given as duplicate-free lists of points in any
order), at every width `w ≥ b(⌊log₂(L + M + 2)⌋ + 1)` (`L` the number of input words, `M` the
largest one) and on every coin sequence, the run halts within `C(N + 1)^d log₂(N + 2)` steps
and outputs exactly the set `A + B`, without repetition. -/
theorem lemma_2_3 (d : ℕ) : ∃ (P : List Instr) (b C : ℕ),
    ∀ (N : ℕ) (A B : Finset (Fin d → ℕ)) (lA lB : List (Fin d → ℕ)),
      InCube N A → InCube N B → ListsSet lA A → ListsSet lB B →
      ∀ w : ℕ, widthMin b (sumsetInput N lA lB).length (maxWord (sumsetInput N lA lB)) ≤ w →
        ∀ ω : Coins, ∃ mem, runFor P w (sumsetInput N lA lB)
            (C * ((N : ℝ) + 1) ^ d * Real.logb 2 ((N : ℝ) + 2)) ω = some mem ∧
          OutputsNatSet mem (A + B) := by sorry

end RelatedSchedFPTAS796.Main
