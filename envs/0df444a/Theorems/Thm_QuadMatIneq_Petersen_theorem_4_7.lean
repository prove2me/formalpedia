-- Prove2me | Theorems.Thm_QuadMatIneq_Petersen_theorem_4_7
-- name    : QuadMatIneq.Petersen.theorem_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:28.319553+00:00
-- url     : https://prove2.me/theorems/4fe9b961-6efd-4416-ab5b-2d3ecbebb85a
-- title:
--   Theorem 4.7 (Matrix S-lemma), p. 12 — for $N\in\boldsymbol\Pi_{q,r}$ with a positive eigenvalue: $\mathcal Z_r(N)\subseteq\mathcal Z_r(M)$ iff $M-\alpha N\geqslant0$, some $\alpha\geqslant0$
-- statement:
--   Let $M,N\in\mathbb S^{q+r}$ be symmetric matrices, partitioned as in (4.1) with upper-left blocks of size $q\times q$.
--
--   1. If there exists a real $\alpha\geqslant0$ such that $M-\alpha N\geqslant0$, then $\mathcal Z_r(N)\subseteq\mathcal Z_r(M)$.
--   2. Assume in addition that $N\in\boldsymbol\Pi_{q,r}$ and that $N$ has at least one positive eigenvalue. Then
--   $$\mathcal Z_r(N)\subseteq\mathcal Z_r(M)\iff\exists\,\alpha\geqslant0:\ M-\alpha N\geqslant0 .$$
--
--   This is the matrix version of the S-lemma under the ordinary Slater condition ($N$ has a positive eigenvalue). It yields the non-strict form of Petersen's lemma.
--
--   **Formalization Note** "At least one positive eigenvalue" is stated through Mathlib's eigenvalues of the symmetric matrix $N$ (`hN.eigenvalues`). The two block index sets are arbitrary finite types.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Theorem 4.7, p. 12

import Mathlib
import Definitions.Def_QuadMatIneq_Petersen_QMI

namespace QuadMatIneq.Petersen
open Matrix
theorem theorem_4_7 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    ((∃ α : ℝ, 0 ≤ α ∧ (M - α • N).PosSemidef) → ZSet N ⊆ ZSet M) ∧
    (InPi N → (∃ i, 0 < hN.eigenvalues i) →
      (ZSet N ⊆ ZSet M ↔ ∃ α : ℝ, 0 ≤ α ∧ (M - α • N).PosSemidef)) := by sorry
end QuadMatIneq.Petersen
