-- Prove2me | Theorems.Thm_QAlgorithms_Childs_subadditivity_of_errors
-- name    : QAlgorithms.Childs.subadditivity_of_errors
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:31:36.472888+00:00
-- url     : https://prove2.me/theorems/bf85f8e8-a496-46a6-ab20-9ebdded7831c
-- title:
--   Subadditivity of errors in products of unitaries
-- statement:
--   Let $U_1,\dots,U_t$ and $V_1,\dots,V_t$ be unitary matrices of the same (finite) dimension, and let $\epsilon\in\mathbb R$. Suppose $\|U_i-V_i\|\le\epsilon$ for every $i\in\{1,\dots,t\}$, where $\|\cdot\|$ is the spectral norm. Then
--
--   $$
--   \|U_t\cdots U_2U_1-V_t\cdots V_2V_1\|\le t\epsilon .
--   $$
--
--   So errors in approximating the gates of a circuit add up at most linearly. To simulate a $t$-gate circuit to total error $\epsilon$, it is enough to simulate each gate to error $\epsilon/t$.
--
--   **Formalization Note** The indices are $0,\dots,t-1$ in Lean, and the product is taken with the highest index on the left. For $t=0$ both products are the identity.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 15, Lemma 2.2. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Circuit
set_option autoImplicit false

namespace QAlgorithms.Childs

open QAlgorithms


/-- Childs, Lemma 2.2 (subadditivity of errors), PDF p. 15. If `U_i`, `V_i` are unitary
matrices with `‖U_i − V_i‖ ≤ ϵ` (spectral norm) for all `i ∈ {1, …, t}`, then
`‖U_t ⋯ U_2 U_1 − V_t ⋯ V_2 V_1‖ ≤ t ϵ`. Here the source's `U_i` is `U (i − 1)` and
`orderedProd U = U (t − 1) * ⋯ * U 0`. -/
theorem subadditivity_of_errors {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℕ)
    (U V : Fin t → Matrix.unitaryGroup ι ℂ) (ε : ℝ)
    (h : ∀ i, specNorm ((U i : Matrix ι ι ℂ) - (V i : Matrix ι ι ℂ)) ≤ ε) :
    specNorm (orderedProd (fun i => (U i : Matrix ι ι ℂ)) -
      orderedProd (fun i => (V i : Matrix ι ι ℂ))) ≤ t * ε := by
  sorry


end QAlgorithms.Childs
