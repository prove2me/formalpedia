-- Prove2me | Theorems.Thm_QuantumScalingMWPM_QLiquidationist_lemma_1
-- name    : QuantumScalingMWPM.QLiquidationist.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:55.370973+00:00
-- url     : https://prove2.me/theorems/b67674d8-4abe-4252-a14a-ddcf1bd6a294
-- title:
--   Lemma 1 — Grover/BBHT search in the QRAM model: $\tilde O(\sqrt{N/k})$ time, any inverse-polynomial failure
-- statement:
--   Let $f$ be a predicate on the domain $[N]=\{1,\dots,N\}$ that is computable in constant time from the memory, that is, by a fixed straight-line word-RAM predicate program $F$ reading the memory list $I$, where $N=I[0]$. Let $K=\{x\in[N]: f(x)=1\}$ and $k=|K|$.
--
--   For every constant $c>0$ and every such $F$ there are a QRAM program $A$ and constants $C>0$ and $\kappa\in\mathbb N$ such that, on every memory $I$, the following holds with probability at least $1-(N+2)^{-c}$: $A$ halts within time
--   $$C\Bigl(1+\sqrt{N/\max(1,k)}\Bigr)\bigl(\log_2(N+2)\bigr)^{\kappa}$$
--   with all registers within the word length, and
--   1. if $k\ge1$, it outputs some $x\in K$;
--   2. if $k=0$, it outputs $\bot$ (the empty list), in time $\tilde O(\sqrt N)$.
--
--   The polylogarithmic factor absorbs the logarithmic number of repetitions that reduce the failure probability to $(N+2)^{-c}$. This is the search primitive behind every GROVERSEARCH call of QUANTUMPATHSEARCH, and its running-time analysis (Lemma 2) charges each call by this bound.
--
--   Differences from the source:
--   - encoding: a predicate f on [N] computable in constant time, with access to the memory → f(x) = evalPred F I x for a fixed straight-line predicate program F over const, copy, +, −, ×, ÷, mod, load, =, <, and, not, reading the memory list I; the program A may depend on F; reason: a constant-time word-RAM predicate is such a program, since branches of constant length are expressible arithmetically; the constants of the time bound depend on f, as in the source
--   - encoding: time Õ(√(N/k)) when k ≥ 1 and Õ(√N) when k = 0; failure probability any inverse polynomial → for every c > 0: probability ≥ 1 − (N+2)^{−c} of halting with cost ≤ C(1 + √(N/max(1,k)))(log₂(N+2))^κ, within the word length, with the correct output (some x ∈ K, or the empty list for ⊥); reason: Õ hides polylog factors in N; every inverse polynomial in N is at most (N+2)^{−c} for some c, so ∀ c covers "any inverse polynomial", including N ≤ 1 where the source still claims bounded error; the additive 1 only matters at N = 0; ⊥ is the empty output list
--   - encoding: domain [N] and the predicate's arrays → N = I[0] (as a natural number) and f reads the input list I, out-of-range reads give 0; reason: the arrays the predicate reads are given as the program's input; nothing else is fixed
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), Lemma 1, p. 11 (imported from Boyer–Brassard–Høyer–Tapp [6]); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/842.pdf

import Mathlib
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_Machine

namespace QuantumScalingMWPM.QLiquidationist

open scoped Classical

/-- Lemma 1 (Grover/BBHT search, p. 11), in the QRAM model. For every constant `c > 0` and every
predicate `f` computable in constant time (a fixed straight-line predicate program `F` reading the
memory `I`) there are a program and constants `C > 0`, `k` such that on every memory `I` with
`N = I[0]` and `K = {x ∈ [N] : f(x)}`: with probability at least `1 − (N + 2)^{−c}` (every
inverse polynomial in `N`, also for `N ≤ 1`) the program halts
within `C (1 + √(N / max(1, |K|))) (log₂(N + 2))^k` time, within the word length, and outputs some
`x ∈ K` if `K ≠ ∅`, and `⊥` (the empty list) if `K = ∅`. -/
theorem lemma_1 (c : ℝ) (hc : 0 < c) (F : List PInstr) :
    ∃ (A : Program) (width : ℕ) (C : ℝ) (k : ℕ), 0 < C ∧ ∀ I : List ℤ,
      let N : ℕ := (I.headD 0).toNat
      let K : Finset ℕ := (Finset.Icc 1 N).filter fun x => evalPred F I x
      let B : ℝ := C * (1 + Real.sqrt ((N : ℝ) / ((max 1 K.card : ℕ) : ℝ))) *
        (Real.logb 2 ((N : ℝ) + 2)) ^ k
      1 - ((N : ℝ) + 2) ^ (-c) ≤
        succProb A (wordBits width I) ⌊B⌋₊ (initState I) fun s =>
          (s.cost : ℝ) ≤ B ∧ s.peak < 2 ^ wordBits width I ∧
            (K.Nonempty → ∃ x ∈ K, outputOf s = [(x : ℤ)]) ∧ (K = ∅ → outputOf s = []) := by sorry

end QuantumScalingMWPM.QLiquidationist
