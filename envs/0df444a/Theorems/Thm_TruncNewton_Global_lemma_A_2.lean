-- Prove2me | Theorems.Thm_TruncNewton_Global_lemma_A_2
-- name    : TruncNewton.Global.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:09:46.959192+00:00
-- url     : https://prove2.me/theorems/47df803a-ac61-4560-be87-50c5951bdb7d
-- title:
--   Lemma A.2 — descent and direction bounds
-- statement:
--   Fix $n$, $\varepsilon>0$, and an upper bound $M>0$ on the norm of a self-adjoint Hessian operator $H$. There are positive constants $\gamma_0,\gamma_1$, uniform over every $H$ with $\|H\|\le M$, every vector $g$, every forcing value $\eta$, and every TNCG direction $p$, such that
--
--   $$\langle g,p\rangle\le-\gamma_0\|g\|^2,\qquad \|p\|\le\gamma_1\|g\|.$$
--
--   The bounds ensure that the minor iteration supplies a controlled descent direction for the major line search.
--
--   **Formalization Note** The paper's proof chooses $\gamma_0=\min\{1,1/\|H\|\}$ and $\gamma_1=\max\{n/\varepsilon,1\}$. A positive norm bound $M$ expresses their uniform dependence without dividing by zero when $H=0$. The dimension is fixed by the Euclidean space.
-- source:
--   Dembo and Steihaug, Truncated-Newton algorithms for large-scale unconstrained optimization, Math. Programming 26 (1983), pp. 206–207, Lemma A.2, (A.8)–(A.9), https://doi.org/10.1007/BF02592055

import Mathlib
import Definitions.Def_TruncNewton_Global_Setting

namespace TruncNewton.Global

theorem lemma_A_2 {n : ℕ} (ε : ℝ) (hε : 0 < ε) (M : ℝ) (hM : 0 < M) :
    ∃ γ₀ γ₁ : ℝ, 0 < γ₀ ∧ 0 < γ₁ ∧
      ∀ (H : E n →L[ℝ] E n) (g : E n) (η : ℝ) (p : E n),
        IsSelfAdjoint H → ‖H‖ ≤ M → IsTNCGDirection H g ε η p →
          inner ℝ g p ≤ -γ₀ * ‖g‖ ^ 2 ∧ ‖p‖ ≤ γ₁ * ‖g‖ := by sorry

end TruncNewton.Global
