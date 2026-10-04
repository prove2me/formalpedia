-- Prove2me | Theorems.Thm_StabGen_RKHS_squared_norm_bound
-- name    : StabGen.RKHS.squared_norm_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:56:33.318809+00:00
-- url     : https://prove2.me/theorems/4df83bad-ca41-4367-9f2f-d9218a43838b
-- title:
--   Theorem 22 proof — squared norm bound
-- statement:
--   Let $H$ be a real RKHS with evaluation $f(x)$ and let $c$ be $\sigma$-admissible with respect to its functions. Fix $\lambda>0$, a sample of size $m$, and a deleted index $i$. If $f$ minimizes the full squared-norm regularized objective (19) and $f^{\setminus i}$ minimizes the truncated objective (20), then
--   $$2\|f^{\setminus i}-f\|_K^2\le\frac{\sigma}{\lambda m}\left|(f^{\setminus i}-f)(x_i)\right|.$$
--
--   This is the first quantitative step in the proof of Theorem 22.
--
--   **Formalization Note** Both minimizations are over the entire RKHS; (20) retains the factor $1/m$.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 515 (PDF p. 17), Proof of Theorem 22, https://jmlr.org/papers/v2/bousquet02a.html

import Mathlib
import Definitions.Def_StabGen_RKHS_Regularization
import Definitions.Def_FoundationsML_Stability_IsRKHSOf

namespace StabGen.RKHS

open FoundationsML.Stability

/-- Proof of Theorem 22, p. 515: the squared RKHS norm bound for the
minimizers of equations (19) and (20). -/
theorem squared_norm_bound {X Y H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {m : ℕ}
    (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ)
    (c : ℝ → Y → ℝ) (σ lam : ℝ) (S : Fin m → X × Y)
    (i : Fin m) (f f' : H)
    (hRKHS : IsRKHSOf K Φ ev)
    (hσ : SigmaAdmissible (Set.range ev) c σ) (hlam : 0 < lam)
    (hmin : ∀ g : H, regRisk c ev S lam (fun h : H => ‖h‖ ^ 2) f ≤
      regRisk c ev S lam (fun h : H => ‖h‖ ^ 2) g)
    (hmin' : ∀ g : H, truncRegRisk c ev S i lam (fun h : H => ‖h‖ ^ 2) f' ≤
      truncRegRisk c ev S i lam (fun h : H => ‖h‖ ^ 2) g) :
    2 * ‖f' - f‖ ^ 2 ≤ (σ / (lam * (m : ℝ))) * |ev (f' - f) (S i).1| := by sorry

end StabGen.RKHS
