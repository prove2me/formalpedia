-- Prove2me | Theorems.Thm_QAlgorithms_Childs_periodFindingReals_convergent
-- name    : QAlgorithms.Childs.periodFindingReals_convergent
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:31:19.068066+00:00
-- url     : https://prove2.me/theorems/49fe56f2-c1a9-4552-97d1-392b1da2e079
-- title:
--   Period finding over the reals: an irrational period from two Fourier samples
-- statement:
--   This is the classical post-processing step of period finding over the reals (Childs, Lemma 9.1).
--
--   Write $\lfloor x \rceil$ for the integer nearest to the real number $x$. Let $r > 0$ be a real number (the period, possibly irrational), let $N$ be a positive integer (the size of the cyclic group $\mathbb Z_N$ used for Fourier sampling), and let $j, j'$ be relatively prime integers with $1 \le j < r$ and $1 \le j' < r$; Fourier sampling returns the integers $\lfloor jN/r \rceil$ and $\lfloor j'N/r \rceil$. If $N \ge 3r^2$, then:
--
--   1. the fraction $j/j'$ is one of the convergents of the continued fraction expansion of the rational number
--   $$
--   \frac{\lfloor jN/r \rceil}{\lfloor j'N/r \rceil};
--   $$
--   2. the period is recovered to within one unit:
--   $$
--   \left| r - \left\lfloor \frac{jN}{\lfloor jN/r \rceil} \right\rceil \right| \le 1.
--   $$
--
--   Thus, from two samples with coprime multipliers, one learns $j$ from the continued fraction expansion and then an approximation of $r$ to within $1$.
--
--   **Formalization Note** The nearest-integer function is Mathlib's `round` (ties rounded up; the source leaves ties unspecified and its proof uses only that the rounding error is at most $1/2$). Convergents are Mathlib's `Real.convergent`, which coincide with the convergents of the regular continued fraction. The ranges $1 \le j, j' < r$ are those the source's proof uses (they come from $\lfloor jN/r \rceil \in \mathbb Z_N$ and the proof's appeals to $j \ge 1$ and $j' < r$); the proof's "$j < j'$ without loss of generality" is not imposed. Under these hypotheses the denominator $\lfloor j'N/r \rceil$ is at least $3$, so no division by zero occurs.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 48, Lemma 9.1. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Basic
set_option autoImplicit false

namespace QAlgorithms.Childs

/-- Childs, Lemma 9.1 (PDF p. 48, proof p. 49): recovering an irrational period from two
Fourier samples. Let `r > 0` be a real period, let `j, j'` be relatively prime positive integers
below `r` (the multiples `⌊jN/r⌉, ⌊j'N/r⌉` returned by Fourier sampling over `Z_N`, §9.2,
PDF p. 48), and let `N ≥ 3r²`. Then `j/j'` appears as a convergent in the continued fraction
expansion of `⌊jN/r⌉/⌊j'N/r⌉`, and `|r − ⌊jN/⌊jN/r⌉⌉| ≤ 1`. -/
theorem periodFindingReals_convergent (r : ℝ) (N j j' : ℕ) (hj : 1 ≤ j) (hj' : 1 ≤ j')
    (hjr : (j : ℝ) < r) (hj'r : (j' : ℝ) < r) (hcop : Nat.Coprime j j')
    (hN : 3 * r ^ 2 ≤ (N : ℝ)) :
    (∃ n : ℕ, Real.convergent
        ((round ((j : ℝ) * N / r) : ℝ) / (round ((j' : ℝ) * N / r) : ℝ)) n =
        ((j : ℚ) / (j' : ℚ))) ∧
      |r - (round ((j : ℝ) * N / (round ((j : ℝ) * N / r) : ℝ)) : ℝ)| ≤ 1 := by
  sorry

end QAlgorithms.Childs
