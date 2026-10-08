-- Prove2me | Theorems.Thm_TensorNP_Bilinear_minors_vanish_iff_proportional
-- name    : TensorNP.Bilinear.minors_vanish_iff_proportional
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:56.495002+00:00
-- url     : https://prove2.me/theorems/65a99bc2-6852-417f-ba54-2f45b442dfd7
-- title:
--   Proof of Theorem 3.7 — the $2\times2$ minors of $[\mathbf v\ \mathbf w]$ vanish iff $\mathbf v = c\mathbf w$
-- statement:
--   Let $\mathbf v, \mathbf w \in \mathbb C^N$ be **nonzero** vectors, and for each pair of indices $a < b$ let $A_{(a,b)}$ be the $\{-1,0,1\}$-matrix with $\mathbf v^\top A_{(a,b)} \mathbf w = v_a w_b - v_b w_a$, the $2\times 2$ minor of rows $a, b$ of the $N\times 2$ matrix $[\mathbf v\ \mathbf w]$. Then
--   $$
--   \mathbf v^\top A_{(a,b)} \mathbf w = 0 \ \text{ for all } a < b \iff \exists\, c \in \mathbb C:\ \mathbf v = c\,\mathbf w .
--   $$
--
--   In the proof of Theorem 3.7 ($N = 2v+1$) these minors are the first $v(2v+1)$ slices of $\mathcal A_G$; they force the two vectors of a solution to be proportional, which turns the bilinear system back into the quadratic system $C_G$.
--
--   **Formalization Note** The paper says the minors "have a common nontrivial zero $\mathbf v, \mathbf w$ iff $\mathbf v = c\mathbf w$"; "nontrivial" is read as both $\mathbf v$ and $\mathbf w$ nonzero, as in Problem 3.1. Without $\mathbf w \neq 0$ the claim is false ($\mathbf w = 0 \neq \mathbf v$ makes every minor vanish). The statement is given for every length $N$; the proof uses $N = 2v+1$.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:17, proof of Theorem 3.7 (the 2 × 2 minors)

import Mathlib
import Definitions.Def_TensorNP_Bilinear_Construction

namespace TensorNP.Bilinear

/-- Proof of Theorem 3.7 (p. 0:17), the 2×2 minors: for nonzero `v, w ∈ ℂ^N`, all the minors
`vᵀ A_{(a,b)} w = v_a w_b − v_b w_a` (`a < b`) vanish iff `v = c w` for some `c ∈ ℂ`. -/
theorem minors_vanish_iff_proportional {N : ℕ} (v w : Fin N → ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    (∀ ab : MinorIdx N, ∑ p, ∑ q, (minorSlice ab p q : ℂ) * v p * w q = 0) ↔
      ∃ c : ℂ, v = c • w := by sorry

end TensorNP.Bilinear
