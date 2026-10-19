-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_quantumSearch_unknownCount_sqrt
-- name    : QAlgorithms.Nannicini.quantumSearch_unknownCount_sqrt
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:46:28.709458+00:00
-- url     : https://prove2.me/theorems/625e4f28-05f9-4df9-993d-cee25e87516f
-- title:
--   Search without knowing |M| with O(√(2^n/|M|)) expected oracle calls
-- statement:
--   Let $U_f$ be the binary oracle $|j\rangle|y\rangle \mapsto |j\rangle|y \oplus f(j)\rangle$ of a Boolean function $f : \{0,1\}^n \to \{0,1\}$, and let $M = \{j \in \{0,1\}^n : f(j) = 1\}$ be the set of marked elements. Algorithm 1, which receives only $U_f$ (not $|M|$), satisfies the following: there is an absolute constant $C > 0$ such that for every $n$ and every $f$ with $M \neq \emptyset$, the algorithm returns an element of $M$ with probability one and
--
--   $$
--   \mathbb{E}[\#\text{applications of } U_f] \le C\sqrt{\frac{2^n}{|M|}}.
--   $$
--
--   This is the quadratic speedup of Grover search, obtained without prior knowledge of the number of solutions.
--
--   **Formalization Note** That the algorithm does not use $|M|$ is structural: the Lean object describing Algorithm 1 depends on $f$ only. The hypothesis $M \neq \emptyset$ is implicit in "determines an element of $M$".
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 94, Corollary 4.30. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
import Definitions.Def_QAlgorithms_Nannicini_Ch04c_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open scoped ENNReal



/-- Nannicini p.94, Corollary 4.30: there is a constant `C > 0` such that for every `n` and every
Boolean function `f : {0,1}^n → {0,1}` with a nonempty set `M = {j : f(j) = 1}` of marked
elements, Algorithm 1 (whose input is only the oracle `U_f`, not `|M|`) returns an element of `M`
with probability one, using at most `C √(2^n/|M|)` applications of `U_f` in expectation. -/
theorem quantumSearch_unknownCount_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Qubits n → Bool),
      1 ≤ (Finset.univ.filter fun j => f j = true).card →
        (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc) = 1 ∧
        (∀ oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc ≠ 0 →
          ∃ j, oc.1 = some j ∧ f j = true) ∧
        searchAlg1ExpectedCost f ≤
          ENNReal.ofReal (C * Real.sqrt ((2 : ℝ) ^ n /
            ((Finset.univ.filter fun j => f j = true).card : ℝ))) := by
  sorry









end QAlgorithms.Nannicini
