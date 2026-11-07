-- Prove2me | Theorems.Thm_QCopyMono_walk_change
-- name    : QCopyMono.walk_change
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:34.426598+00:00
-- url     : https://prove2.me/theorems/82cdfdd1-633e-47a2-ba68-9abc5bed85f0
-- title:
--   Proofs of Lemmas 6–7, pp.37, 40 — walk-change bounds $2CI[h]/n$ per step and $2CjI[h]/n$ over $j$ steps
-- statement:
--   There are absolute constants $C,n_0>0$ such that for $n\ge n_0$, $n^{-1/2}\le\varepsilon\le1/2$ and every $h:\{0,1\}^n\to\{0,1\}$, with $Y$ uniform on $\{0,1\}^n$ and $\mathcal B$ the Hamming band:
--
--   1. for an upward walk $U_0=Y,U_1,\dots$ (each step sets one uniformly random remaining zero coordinate to one), and likewise for a downward walk, the probability of starting in $\mathcal B$ and traversing an edge on which $h$ changes at step $i+1$ satisfies
--   $$
--   \Pr\big[Y\in\mathcal B,\ h(U_i)\neq h(U_{i+1})\big]\le\frac{2C\,I[h]}{n}\qquad\text{whenever } i+1\le\varepsilon\sqrt n;
--   $$
--   2. by a union bound over the steps, $\Pr[Y\in\mathcal B,\ h(Y)\neq h(Y^{\uparrow j})]\le 2C\,j\,I[h]/n$, and likewise downward, whenever $j\le\varepsilon\sqrt n$;
--   3. if moreover $I[h]\le10\sqrt n$, these bounds are at most $20C/\sqrt n$ and $20C\,j/\sqrt n$.
--
--   In the paper this is applied to $\tilde f$ with $t_d-1$ steps in the proof of Lemma 6 and to $f$ with $t_d$ steps in the proof of Lemma 7.
--
--   Differences from the source:
--   - generalization: the truncated f̃ with t_d − 1 steps (p.37), and f with t_d ≤ max{1, ε√n} steps (p.40) → every h and every number of steps j ≤ ε√n (per step: i + 1 ≤ ε√n), upward and downward; reason: both printed uses are instances (in the range ε ≥ n^{-1/2}, t_d ≤ ε√n), and the argument uses only the step count
--   - encoding: the step-by-step walk U_0 = Y, …, U_j → the endpoint after j steps as a uniformly random j-subset of the zero (one) coordinates, and step i+1 as one further uniformly random remaining coordinate; reason: the two descriptions have the same law
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), proof of Lemma 6, pp.36–37; proof of Lemma 7, p.40

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_Influence
import Definitions.Def_QCopyMono_PathExperiment

namespace QCopyMono

open QAlgorithms

/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), proof of Lemma 6, pp.36–37, and proof of
Lemma 7, p.40: the walk-change bound. There are absolute constants `C, n₀ > 0` such that for
`n ≥ n₀`, `n^{−1/2} ≤ ε ≤ 1/2` and every `h : {0,1}ⁿ → {0,1}`:

1. (per step) for an upward or downward walk from a uniform `Y`, the probability of starting in
   `𝓑` and traversing an edge on which `h` changes at step `i + 1` is at most `2C I[h]/n`,
   whenever `i + 1 ≤ ε√n`;
2. (union bound over the steps) `Pr[Y ∈ 𝓑, h(Y) ≠ h(Y^{↑j})] ≤ 2C j I[h]/n`, and likewise
   downward, whenever `j ≤ ε√n`;
3. if moreover `I[h] ≤ 10√n` (eq. (53)), the two bounds are at most `20C/√n` and `20C j/√n`.

**Formalization Note.** A `j`-step walk is given by the law of its flipped set, a uniformly
random `j`-subset of the zero (one) coordinates; this is the law of the printed step-by-step walk.
In the range `ε ≥ n^{−1/2}` the lengths used on pp.36–37 (`t_d − 1` steps, `t_d ≤ ε√n`) and on
p.40 (`t_d ≤ max{1, ε√n} = ε√n` steps) are covered. -/
theorem walk_change :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ,
      (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ε → ε ≤ 1 / 2 → ∀ h : Qubits n → Bool,
        (∀ i : ℕ, ((i : ℝ) + 1) ≤ ε * Real.sqrt n →
          upStepChange ε i h ≤ 2 * C * influence h / n ∧
            downStepChange ε i h ≤ 2 * C * influence h / n) ∧
        (∀ j : ℕ, (j : ℝ) ≤ ε * Real.sqrt n →
          upChange ε j h ≤ 2 * C * j * influence h / n ∧
            downChange ε j h ≤ 2 * C * j * influence h / n) ∧
        (influence h ≤ 10 * Real.sqrt n →
          (∀ i : ℕ, ((i : ℝ) + 1) ≤ ε * Real.sqrt n →
            upStepChange ε i h ≤ 20 * C / Real.sqrt n ∧
              downStepChange ε i h ≤ 20 * C / Real.sqrt n) ∧
          ∀ j : ℕ, (j : ℝ) ≤ ε * Real.sqrt n →
            upChange ε j h ≤ 20 * C * j / Real.sqrt n ∧
              downChange ε j h ≤ 20 * C * j / Real.sqrt n) := by sorry

end QCopyMono
