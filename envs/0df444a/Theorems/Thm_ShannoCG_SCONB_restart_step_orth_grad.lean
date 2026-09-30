-- Prove2me | Theorems.Thm_ShannoCG_SCONB_restart_step_orth_grad
-- name    : ShannoCG.SCONB.restart_step_orth_grad
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T07:18:45.415873+00:00
-- url     : https://prove2.me/theorems/c34054ed-5928-4043-89ee-528c728ee95e
-- title:
--   $p_t'g_{k+1} = 0$ under exact searches and conjugacy
-- statement:
--   Let $A$ be a real $n\times n$ matrix, $c \in \mathbb R^n$, and gradients $g_i = Ax_i + c$ along iterates with $x_{i+1} = x_i + p_i$ for $t \le i \le k$, where $t < k$. Assume
--
--   1. the restart search is exact: $p_t' g_{t+1} = 0$;
--   2. the restart step is conjugate to the later steps: $p_t' A p_i = 0$ for $i = t+1, \dots, k$.
--
--   Then
--
--   $$p_t' g_{k+1} = 0.$$
--
--   This is the fact, stated in Shanno's proof, that with exact searches on a quadratic the restart step is orthogonal to every later gradient of the cycle; it is what makes the restart matrix act on $g_{k+1}$ in the simple form (42).
--
--   **Formalization Note** The conjugacy of the restart step with the later steps is a hypothesis, as in the paper, which takes it as known for exact searches on a quadratic; it is not derived from a run of the algorithm. No positive definiteness is needed.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, p. 251 (PDF p. 8), §IV, the sentence before eq. (41), the display after it and the sentence after that

import Mathlib

open Matrix

namespace ShannoCG.SCONB

/-- Shanno, *Conjugate Gradient Methods with Inexact Searches*, Math. Oper. Res. 3(3) (1978), §IV, p. 251 (PDF 8), the sentence before (41), the display after (41) and the sentence
after it: with exact searches on a quadratic, `p_t' g_{k+1} = 0`. The paper's argument uses
`p_t' g_{t+1} = 0` (exact search at the restart step) and the conjugacy
`p_t' A p_i = 0`, `i = t+1, …, k`.

**Formalization Note.** Gradient `g i = A *ᵥ x i + c` (arbitrary `c`), steps `x_{i+1} = x_i + p_i`
for `t ≤ i ≤ k`. The exact search at `t` and the conjugacy are the hypotheses `hexact_t` and
`hconj` (the paper states them as known facts for exact searches on a quadratic; they are not
derived here). No positive definiteness is needed. -/
theorem restart_step_orth_grad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (x p g : ℕ → Fin n → ℝ) (t k : ℕ) (htk : t < k)
    (hg : ∀ i, g i = A *ᵥ x i + c)
    (hstep : ∀ i, t ≤ i → i ≤ k → x (i + 1) = x i + p i)
    (hexact_t : p t ⬝ᵥ g (t + 1) = 0)
    (hconj : ∀ i, t < i → i ≤ k → p t ⬝ᵥ (A *ᵥ p i) = 0) :
    p t ⬝ᵥ g (k + 1) = 0 := by sorry

end ShannoCG.SCONB
