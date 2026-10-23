-- Prove2me | Theorems.Thm_WalledBrauer_SuperSchurWeyl_lemma_7_1
-- name    : WalledBrauer.SuperSchurWeyl.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:06.921975+00:00
-- url     : https://prove2.me/theorems/b50987e1-6300-431b-bbd9-3dc4f400e30e
-- title:
--   Lemma 7.1 — Ω on M ⊗ N for M, N ∈ {V, W}
-- statement:
--   Let $\mathfrak g = \mathfrak{gl}_{m|n}(\mathbb C)$, with $V$ its natural supermodule (basis $v_1, \dots, v_{m+n}$) and $W = V^*$ (dual basis $w_1, \dots, w_{m+n}$), and let $\Omega = \sum_{i,j} (-1)^{|j|} e_{i,j} \otimes e_{j,i}$ be the element (7.2) of $U(\mathfrak g) \otimes U(\mathfrak g)$, acting on $M \otimes N$ through the sign rule. Then, for all $1 \le i, j \le m+n$,
--
--   $$
--   \begin{aligned}
--   \Omega(v_i \otimes v_j) &= (-1)^{|i||j|} v_j \otimes v_i, \\
--   \Omega(w_i \otimes w_j) &= (-1)^{|i||j|} w_j \otimes w_i, \\
--   \Omega(v_i \otimes w_j) &= -\delta_{i,j} (-1)^{|i|} \textstyle\sum_{k=1}^{m+n} v_k \otimes w_k, \\
--   \Omega(w_i \otimes v_j) &= -\delta_{i,j} \textstyle\sum_{k=1}^{m+n} (-1)^{|k|} w_k \otimes v_k .
--   \end{aligned}
--   $$
--
--   The lemma identifies $\Omega$ as a signed flip on $V \otimes V$ and $W \otimes W$, and as a signed contraction followed by the canonical element on $V \otimes W$ and $W \otimes V$. It is the local computation behind the statements that transpositions act as the operators $\Omega_{a,b}$ (Lemmas 7.3 and 7.4).
--
--   **Formalization Note** $M \otimes N$ is the two-slot tensor space with slot pattern `![true, true]`, `![false, false]`, `![true, false]` or `![false, true]` ($V$ = `true`), $\Omega$ is `Omega … 0 1`, and a basis vector $u_i \otimes u_j$ is `Pi.single ![i, j] 1`; colours are 0-based.
-- source:
--   Brundan and Stroppel, Gradings on walled Brauer algebras and Khovanov's arc algebra, arXiv:1107.0999v1, p. 49, Lemma 7.1

import Mathlib
import Definitions.Def_WalledBrauer_SuperSchurWeyl_Weights

namespace WalledBrauer.SuperSchurWeyl

/-- Lemma 7.1 (p. 49): `Ω = Ω_{1,2}` on `M ⊗ N` for `M, N ∈ {V, W}`, on basis vectors
(0-based slots and colours; `κ` gives the slot pattern, `true` = `V`, `false` = `W`). -/
theorem lemma_7_1 (m n : ℕ) (i j : Fin (m + n)) :
    (Omega m n ![true, true] 0 1).mulVec (Pi.single (![i, j] : Idx m n 2) 1) =
        sgn (par m i * par m j) • Pi.single (![j, i] : Idx m n 2) (1 : ℂ) ∧
    (Omega m n ![false, false] 0 1).mulVec (Pi.single (![i, j] : Idx m n 2) 1) =
        sgn (par m i * par m j) • Pi.single (![j, i] : Idx m n 2) (1 : ℂ) ∧
    (Omega m n ![true, false] 0 1).mulVec (Pi.single (![i, j] : Idx m n 2) 1) =
        -((if i = j then sgn (par m i) else 0) • ∑ k : Fin (m + n), Pi.single (![k, k] : Idx m n 2) (1 : ℂ)) ∧
    (Omega m n ![false, true] 0 1).mulVec (Pi.single (![i, j] : Idx m n 2) 1) =
        -((if i = j then (1 : ℂ) else 0) • ∑ k : Fin (m + n), sgn (par m k) • Pi.single (![k, k] : Idx m n 2) (1 : ℂ)) := by sorry

end WalledBrauer.SuperSchurWeyl
