-- Prove2me | Theorems.Thm_RealAPSP_lemma_4_8
-- name    : RealAPSP.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:58:27.553918+00:00
-- url     : https://prove2.me/theorems/af953f89-807f-45f7-aacd-6ef80a586509
-- title:
--   Lemma 4.8 (Hashing Reals to Integers [FPS26, Lemma 3.9])
-- statement:
--   Let $\Delta\ge0$ and let $A\subseteq\mathbb R$ have a given $\Delta$-approximate subset sum cover of rank $(K\log(|A|+2))^{O(1)}$. There is a randomized algorithm in time $\tilde O(|A|+(K\log(|A|+2))^{O(1)})$ computing a function $h:A\to[\pm2^{(K\log(|A|+2))^{O(1)}}]$ such that:
--
--   1. for all $a,b,c\in A$ with $a+b+c=0\pm\Delta$, $\mathbb P[h(a)+h(b)+h(c)=0]\ge p$, for an absolute $p>0$;
--   2. for all $a,b,c\in A$ with $h(a)+h(b)+h(c)=0$, we have $a+b+c=0\pm100\Delta$;
--   3. for all $a,b,c\in A$ with $h(a)+h(b)+h(c)<0$, we have $a+b+c<100\Delta$.
--
--   This is the step that replaces reals by integers while keeping approximate sums and signs. The paper imports it, adding clause 3.
--
--   **Formalization Note** A preprocessor runs in the printed time; an evaluator, from the preprocessor's memory with an element index, then prints $h(a)$ in $\kappa(K\log(|A|+2))^{c'}$ steps.
--
--   Differences from the source:
--   - reading: the comparison-addition model of §1.2, p.3, which also names a "realistic" variant → the machine RealAPSP.Machine: the published GuardedSSSP core plus rneg, unit cost, stuck on word overflow, fair coins preloaded in memory; reason: the realistic variant defers to [FPS26, Section 1.1], which is not held, and Theorem 1.1 does not name it; rneg is simulable at constant overhead by pairs p − q
--   - encoding: input and output as mathematical objects → fixed cell layouts for the parameters, matrices and outputs, given in the docstrings; reason: a machine statement needs a layout; every layout used is within a constant factor of any other
--   - encoding: real parameters K ≥ 1 → natural numbers K ≥ 1 in input cells; reason: the integer bank cannot read a real; the statement at the ceiling of a real K implies it at K: the hypothesis on K implies the one on ⌈K⌉, and the bounds at ⌈K⌉ ≤ 2K are within the O-constants
--   - encoding: log |A| → the logarithm of the argument plus 2; reason: the page writes O-notation for large arguments; the literal formula is 0 at small arguments, where a machine needs at least one step
--   - reading: "computes a function h" in time Õ(|A| + (K log |A|)^{O(1)}) → a preprocessor within that time, and an evaluator printing h(a) in (K log(|A|+2))^{c′} steps; reason: |A| values of poly(K log |A|) bits each exceed the printed time, so an explicit table cannot be meant; the p.14 proof of Lemma 4.9 pays for evaluation separately
--   - encoding: the cover in the hypothesis → the cover in the input; reason: the printed time is below that of computing a cover by Theorem 4.7
--   - reading: clauses (ii) and (iii), with no probability → hold on every coin tape; reason: as printed
--   - encoding: a value of [±2^{…}] → a sign and an array of bits; reason: it does not fit a word
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Lemma 4.8, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_RealAPSP_Cover

namespace RealAPSP

/-- **Lemma 4.8 (Hashing Reals to Integers [FPS26, Lemma 3.9]).** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…), p.13 (PDF p.15). Imported; not proved in this paper, except that (iii) is argued on p.13.

Two programs: the preprocessor `Pre`, on the cover `(α, f)` in its input, within the printed time; then the evaluator `Eval`, from `Pre`'s final memory with an element index `x` written in output cell `0`, which prints `h(x)` in `κ(K log(m+2))^{c'}` steps: the bit
length at output cell `1`, the sign at output cell `2`, the bits from output cell `3`. All steps read the same coin memory, so `h` is a function of the tape. Clauses (ii) and (iii) hold on every tape; (i) is a per-triple law with `p` absolute. -/
theorem lemma_4_8 :
    ∃ p : ℝ, 0 < p ∧ ∀ c₀ : ℕ, ∃ (c' : ℕ) (Pre Eval : Program) (κ : ℝ), ∀ (m K d : ℕ), 1 ≤ m → 1 ≤ K →
      (d : ℝ) ≤ ((K : ℝ) * Real.log ((m : ℝ) + 2)) ^ c₀ → ∀ Δ : ℝ, 0 ≤ Δ →
      ∀ (a : Fin m → ℝ), Function.Injective a → ∀ (α : Fin d → ℝ) (f : Fin m → Fin d → Bool), IsSubsetSumCover Δ a d α f →
        let width := m + K + d + 2
        let ints : List ℤ := [(m : ℤ), (K : ℤ), (d : ℤ)] ++ coverInts f
        let reals : List ℝ := Δ :: coverReals a α
        let T : ℝ := κ * ((m : ℝ) + ((K : ℝ) * Real.log ((m : ℝ) + 2)) ^ c') * Real.log ((m : ℝ) + K + 2) ^ κ
        let TE : ℝ := κ * ((K : ℝ) * Real.log ((m : ℝ) + 2)) ^ c'
        let out : (ℕ → Bool) → Fin m → State := fun tape x =>
          resume Eval width (restart (finalState Pre width tape ints reals T) (outCell 0) ((x : ℕ) : ℤ)) TE
        let bits : (ℕ → Bool) → Fin m → ℕ := fun tape x => ((out tape x).imem (outCell 1)).toNat
        let h : (ℕ → Bool) → Fin m → ℤ := fun tape x => readSigned (out tape x) 2 (bits tape x)
        (∀ tape, HaltsBy Pre width tape ints reals T) ∧
        (∀ tape x, (out tape x).halted = true ∧ (bits tape x : ℝ) ≤ ((K : ℝ) * Real.log ((m : ℝ) + 2)) ^ c') ∧
        (∀ x y z, |a x + a y + a z| ≤ Δ →
          ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ ENNReal.ofReal p ≤ coinTape E ∧
            ∀ tape ∈ E, h tape x + h tape y + h tape z = 0) ∧
        (∀ tape x y z, h tape x + h tape y + h tape z = 0 → |a x + a y + a z| ≤ 100 * Δ) ∧
        (∀ tape x y z, h tape x + h tape y + h tape z < 0 → a x + a y + a z < 100 * Δ) := by sorry

end RealAPSP
