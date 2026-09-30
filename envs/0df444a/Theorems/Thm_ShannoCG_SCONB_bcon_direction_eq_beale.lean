-- Prove2me | Theorems.Thm_ShannoCG_SCONB_bcon_direction_eq_beale
-- name    : ShannoCG.SCONB.bcon_direction_eq_beale
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T07:53:13.245983+00:00
-- url     : https://prove2.me/theorems/56d669ae-8e34-459d-b07a-518973834dff
-- title:
--   On a quadratic with exact searches, the unscaled two-update direction is Beale's direction
-- statement:
--   Under the same hypotheses as for the self-scaled method — $A$ symmetric positive definite, $g_i = Ax_i + c$, $y_i = g_{i+1} - g_i$, and for $t \le i \le k$ (with $t < k$): $x_{i+1} = x_i + p_i$, $p_i = \alpha_i d_i$, exact searches $p_i'g_{i+1} = 0$, conjugacy $p_t'Ap_i = 0$ for $t < i \le k$, and $p_t, p_k \ne 0$ — the unscaled two-update direction $d_{k+1} = -\hat H_{k+1} g_{k+1}$ ($\hat H_k$ from (31), $\hat H_{k+1}$ its BFGS update with $(p_k, y_k)$) is exactly Beale's direction:
--
--   $$d_{k+1} = -g_{k+1} + \frac{y_k' g_{k+1}}{d_k' y_k}\, d_k + \frac{y_t' g_{k+1}}{d_t' y_t}\, d_t.$$
--
--   This is the paper's remark that "an identical argument demonstrates the result for the algorithm defined by (34)–(36)"; here the scale factor is $1$.
--
--   **Formalization Note** Same conventions as the self-scaled statement: gradient $Ax + c$, conjugacy as a hypothesis, nonzero restart and current steps, and Beale's direction in the $d$-form of (28).
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, p. 251 (PDF p. 8), §IV, 'An identical argument demonstrates the result for the algorithm defined by (34)–(36)'

import Mathlib
import Definitions.Def_ShannoCG_SCONB_bconDirection
import Definitions.Def_ShannoCG_SCONB_bealeDirection

open Matrix

namespace ShannoCG.SCONB

/-- Shanno, *Conjugate Gradient Methods with Inexact Searches*, Math. Oper. Res. 3(3) (1978), §IV, p. 251 (PDF 8): "An identical argument demonstrates the result for the algorithm
defined by (34)–(36)." For the unscaled two-update algorithm, `d_{k+1} = −Ĥ_{k+1} g_{k+1}` with
`Ĥ_k` from (31) and `Ĥ_{k+1}` from (32), the direction is exactly Beale's direction (28) (scale 1).

**Formalization Note.** Vectors are `Fin n → ℝ`, `u'v` is `u ⬝ᵥ v`. The quadratic (4) enters
through its gradient `g i = A *ᵥ x i + c` with `A` symmetric positive definite (`A.PosDef`) and
arbitrary `c` ((4) is `c = −A x̂`). Iterates are indexed by `ℕ`; the restart index is `t` and the
claim is for the non-restart steps `k ≥ t + 1` (at `k = t` the paper uses (26) instead); the upper
limit `k ≤ t + n − 1` of (28) is not used and not assumed. Hypotheses: steps `x_{i+1} = x_i + p_i`
and `p_i = α_i d_i` (9) for `t ≤ i ≤ k`; exact searches `p_i'g_{i+1} = 0` (5) for `t ≤ i ≤ k`; the
conjugacy `p_t' A p_i = 0` for `t < i ≤ k`, which the paper takes as known for exact searches on a
quadratic and which is not derived here; and `p_t ≠ 0`, `p_k ≠ 0`, implicit in the paper
(they make every denominator nonzero and force `α_t, α_k ≠ 0`). Beale's direction is written in
the `d`-form of (28). -/
theorem bcon_direction_eq_beale {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (c : Fin n → ℝ)
    (x p d g y : ℕ → Fin n → ℝ) (α : ℕ → ℝ) (t k : ℕ) (htk : t < k)
    (hg : ∀ i, g i = A *ᵥ x i + c)
    (hy : ∀ i, y i = g (i + 1) - g i)
    (hstep : ∀ i, t ≤ i → i ≤ k → x (i + 1) = x i + p i)
    (hpd : ∀ i, t ≤ i → i ≤ k → p i = α i • d i)
    (hexact : ∀ i, t ≤ i → i ≤ k → p i ⬝ᵥ g (i + 1) = 0)
    (hconj : ∀ i, t < i → i ≤ k → p t ⬝ᵥ (A *ᵥ p i) = 0)
    (hpt : p t ≠ 0) (hpk : p k ≠ 0) :
    bconDirection (p t) (y t) (p k) (y k) (g (k + 1)) =
      bealeDirection (g (k + 1)) (d k) (y k) (d t) (y t) := by sorry

end ShannoCG.SCONB
