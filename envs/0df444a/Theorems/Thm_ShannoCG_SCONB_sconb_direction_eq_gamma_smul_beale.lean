-- Prove2me | Theorems.Thm_ShannoCG_SCONB_sconb_direction_eq_gamma_smul_beale
-- name    : ShannoCG.SCONB.sconb_direction_eq_gamma_smul_beale
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T07:47:37.406122+00:00
-- url     : https://prove2.me/theorems/3a9a0776-d053-4b10-9c30-886103a3efe9
-- title:
--   On a quadratic with exact searches, the self-scaled direction is $\gamma_t$ times Beale's direction
-- statement:
--   Let $A$ be a symmetric positive definite $n\times n$ matrix and $c \in \mathbb R^n$, so that $g(x) = Ax + c$ is the gradient of a strictly convex quadratic. Consider a conjugate gradient cycle restarted at iteration $t$ and a later iteration $k > t$, with iterates $x_i$, directions $d_i$, step lengths $\alpha_i$ and steps $p_i$, gradients $g_i = Ax_i + c$ and gradient changes $y_i = g_{i+1} - g_i$. Assume, for $t \le i \le k$,
--
--   1. $x_{i+1} = x_i + p_i$ and $p_i = \alpha_i d_i$;
--   2. the line searches are exact: $p_i' g_{i+1} = 0$;
--   3. the restart step is conjugate to the later steps: $p_t' A p_i = 0$ for $t < i \le k$;
--   4. $p_t \ne 0$ and $p_k \ne 0$.
--
--   Let $d_{k+1} = -\hat H_{k+1} g_{k+1}$ be Shanno's self-scaled two-update direction ($\hat H_k$ from (37) built from $(p_t, y_t)$, $\hat H_{k+1}$ its BFGS update with $(p_k, y_k)$), and $\gamma_t = p_t'y_t / y_t'y_t$. Then
--
--   $$d_{k+1} = \gamma_t\left(-g_{k+1} + \frac{y_k' g_{k+1}}{d_k' y_k}\, d_k + \frac{y_t' g_{k+1}}{d_t' y_t}\, d_t\right),$$
--
--   that is, $\gamma_t$ times Beale's restart direction (28).
--
--   So on a quadratic with exact line searches the self-scaled method generates exactly Beale's search directions; only their length is scaled by $\gamma_t$. This connects the method to the classical conjugate gradient theory, while its descent property does not depend on exact searches.
--
--   **Formalization Note** The quadratic enters through its gradient $Ax + c$ (the paper's (4) is $c = -A\hat x$). The conjugacy in 3 is a hypothesis, as in the paper's proof; it is not derived from a run of the algorithm. The nonzero-step hypotheses 4 are implicit in the paper; they make every denominator nonzero and force $\alpha_t, \alpha_k \ne 0$. The range $k \le t+n-1$ of (28) is not needed and not assumed. Beale's direction is written with $d_k, d_t$ as in (28); the paper's (44) writes the same vector with $p_k, p_t$.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, pp. 250–251 (PDF pp. 7–8), §IV, the claim 'for f(x) quadratic with exact searches each of the above methods reduces exactly to Beale's method defined by (28)' and eq. (44); Beale's direction eq. (28), p. 249

import Mathlib
import Definitions.Def_ShannoCG_SCONB_gammaScale
import Definitions.Def_ShannoCG_SCONB_sconbDirection
import Definitions.Def_ShannoCG_SCONB_bealeDirection

open Matrix

namespace ShannoCG.SCONB

/-- Shanno, *Conjugate Gradient Methods with Inexact Searches*, Math. Oper. Res. 3(3) (1978), §IV, pp. 250–251 (PDF 7–8), the claim "for f(x) quadratic with exact searches each of
the above methods reduces exactly to Beale's method defined by (28)", for the self-scaled
algorithm (34), (38), (39), with its conclusion (44), p. 251: the search direction
`d_{k+1} = −Ĥ_{k+1} g_{k+1}` (Ĥ_k from (37), Ĥ_{k+1} from (32)) equals `γ_t` times Beale's direction
(28), `γ_t = p_t'y_t / y_t'y_t`.

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
theorem sconb_direction_eq_gamma_smul_beale {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (c : Fin n → ℝ)
    (x p d g y : ℕ → Fin n → ℝ) (α : ℕ → ℝ) (t k : ℕ) (htk : t < k)
    (hg : ∀ i, g i = A *ᵥ x i + c)
    (hy : ∀ i, y i = g (i + 1) - g i)
    (hstep : ∀ i, t ≤ i → i ≤ k → x (i + 1) = x i + p i)
    (hpd : ∀ i, t ≤ i → i ≤ k → p i = α i • d i)
    (hexact : ∀ i, t ≤ i → i ≤ k → p i ⬝ᵥ g (i + 1) = 0)
    (hconj : ∀ i, t < i → i ≤ k → p t ⬝ᵥ (A *ᵥ p i) = 0)
    (hpt : p t ≠ 0) (hpk : p k ≠ 0) :
    sconbDirection (p t) (y t) (p k) (y k) (g (k + 1)) =
      gammaScale (p t) (y t) • bealeDirection (g (k + 1)) (d k) (y k) (d t) (y t) := by sorry

end ShannoCG.SCONB
