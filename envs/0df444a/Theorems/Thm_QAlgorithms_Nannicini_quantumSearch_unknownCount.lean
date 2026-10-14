-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_quantumSearch_unknownCount
-- name    : QAlgorithms.Nannicini.quantumSearch_unknownCount
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:46:18.966237+00:00
-- url     : https://prove2.me/theorems/5ca4733c-b7a2-42db-aab4-b7cac794f53a
-- title:
--   Quantum search without knowing the number of marked items: O(1/θ) expected queries
-- statement:
--   Let $f : \{0,1\}^n \to \{0,1\}$ be accessed through the oracle $U_f : |j\rangle|y\rangle \mapsto |j\rangle|y \oplus f(j)\rangle$, let $M = \{j : f(j) = 1\}$ and let $\theta \in [0, \pi/2]$ be defined by $\sin\theta = \sqrt{|M|/2^n}$. Algorithm 1 runs, for $m = 1, \dots, n-1$ and twice for each $m$, the amplitude estimation circuit with $S = H^{\otimes n}$, the reflection $R|j\rangle = (-1)^{f(j)}|j\rangle$ and $m$ qubits of precision, measures the second register to get $j$ and returns $j$ if $f(j) = 1$; afterwards it enumerates $\{0,1\}^n$ and returns the first marked string, or "no solution". A round with $m$ qubits uses $2^m - 1$ applications of the Grover operator (one application of $U_f$ each) plus one test of $f(j)$.
--
--   There is an absolute constant $C > 0$ such that for every $n$ and every $f$:
--
--   1. if $\theta > 0$, then with probability one Algorithm 1 returns some $j$ with $f(j) = 1$, and
--   $$
--   \mathbb{E}[\#\text{applications of } U_f] \le \frac{C}{\theta};
--   $$
--   2. if $\theta = 0$, then with probability one the algorithm returns "no solution", and every run uses at most $C\cdot 2^n$ applications of $U_f$.
--
--   This is the search algorithm of Boyer, Brassard, Høyer and Tapp in its amplitude-estimation form; it is the subroutine of quantum minimum finding.
--
--   **Formalization Note** The algorithm's output and cost are encoded as a joint distribution on (output, cost) pairs, with `none` standing for "no solution"; the constant $C$ is quantified before $n$ and $f$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 93, Theorem 4.29. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
import Definitions.Def_QAlgorithms_Nannicini_Ch04c_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open scoped ENNReal


/-- Nannicini p.93, Theorem 4.29 (Quantum search; Boyer et al. 1998, Brassard et al. 2002):
there is a constant `C > 0` such that for every `n` and every `f : {0,1}^n → {0,1}`, with
`θ = arcsin √(|M|/2^n)` (`M = {j : f(j) = 1}`), Algorithm 1 (p.94) satisfies:
1. if `θ > 0`, it returns, with probability one, a value `j` with `f(j) = 1`, and the expected
   number of applications of `U_f` is at most `C/θ`;
2. if `θ = 0`, it returns "no solution" (with probability one) and every run uses at most
   `C · 2^n` applications of `U_f`. -/
theorem quantumSearch_unknownCount :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Qubits n → Bool),
      (0 < groverAngle (Finset.univ.filter fun j => f j = true).card (2 ^ n) →
        (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc) = 1 ∧
        (∀ oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc ≠ 0 →
          ∃ j, oc.1 = some j ∧ f j = true) ∧
        searchAlg1ExpectedCost f ≤
          ENNReal.ofReal (C / groverAngle (Finset.univ.filter fun j => f j = true).card (2 ^ n))) ∧
      (groverAngle (Finset.univ.filter fun j => f j = true).card (2 ^ n) = 0 →
        (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc) = 1 ∧
        ∀ oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc ≠ 0 →
          oc.1 = none ∧ (oc.2 : ℝ) ≤ C * 2 ^ n) := by
  sorry










end QAlgorithms.Nannicini
