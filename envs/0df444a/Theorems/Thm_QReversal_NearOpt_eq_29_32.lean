-- Prove2me | Theorems.Thm_QReversal_NearOpt_eq_29_32
-- name    : QReversal.NearOpt.eq_29_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:12.885965+00:00
-- url     : https://prove2.me/theorems/8061ca41-54e4-4457-a150-64140b3b5445
-- title:
--   Proof of Theorem 3, lines (28)–(32), p. 9 — the trace Cauchy–Schwarz step
-- statement:
--   Let $p_l\ge0$ be weights and $\rho_l$ density matrices, and let $\{R^l_i\}_i$, $\{B^l_i\}_i$ be arbitrary finite families of matrices indexed by the same set, for each $l$. Then
--   $$
--   \sum_lp_l\sum_i\bigl|\operatorname{tr}\rho_lR^l_iB^l_i\bigr|^2\;\le\;\sum_lp_l\sum_{i,j}\operatorname{tr}R^l_iB^l_j\rho_lB_j^{l\dagger}R_i^{l\dagger}.
--   $$
--
--   This is the chain (28)–(32): the Cauchy–Schwarz inequality for the Hilbert–Schmidt inner product, $\operatorname{tr}\rho_l=1$, and the addition of the non-negative terms $j\ne i$. In the proof of Theorem 3 the left side bounds the normalization factor needed in line (23).
--
--   **Formalization Note** The traces on the right are of positive semidefinite matrices, hence real; the statement takes their real parts. The families are arbitrary, so the statement does not depend on the singular-value choices made earlier in the proof.
-- source:
--   Barnum, Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, arXiv:quant-ph/0004088v2, p. 9, proof of Theorem 3, lines (28)–(32)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_QReversal_NearOpt_Setting

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

namespace QReversal.NearOpt

theorem eq_29_32 {n L κ : Type*} [Fintype n] [Fintype L] [Fintype κ]
    (p : L → ℝ) (hp : ∀ l, 0 ≤ p l) (ρs : L → Matrix n n ℂ)
    (hρs : ∀ l, IsDensityMatrix (ρs l))
    (Rl Bl : L → κ → Matrix n n ℂ) :
    ∑ l, p l * ∑ i, Complex.normSq (Matrix.trace (ρs l * Rl l i * Bl l i)) ≤
      ∑ l, p l * ∑ i, ∑ j,
        (Matrix.trace (Rl l i * Bl l j * ρs l * (Bl l j)ᴴ * (Rl l i)ᴴ)).re := by sorry

end QReversal.NearOpt
