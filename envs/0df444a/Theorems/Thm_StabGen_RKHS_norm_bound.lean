-- Prove2me | Theorems.Thm_StabGen_RKHS_norm_bound
-- name    : StabGen.RKHS.norm_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:56:42.261584+00:00
-- url     : https://prove2.me/theorems/d7ab6226-c87c-4a28-87dd-7b8f82c166bb
-- title:
--   Theorem 22 proof — RKHS distance bound
-- statement:
--   In the setting of Theorem 22, suppose $K(x,x)\le\kappa^2$ for every $x$, where $\kappa\ge0$. For minimizers $f$ of (19) and $f^{\setminus i}$ of (20),
--   $$\|f^{\setminus i}-f\|_K\le\frac{\kappa\sigma}{2\lambda m}.$$
--
--   The estimate combines the squared-norm and point-evaluation bounds before the final loss comparison.
--
--   **Formalization Note** The nonnegative sign of $\kappa$ is explicit here because the bound is linear in $\kappa$. The $1/m$ normalization of (20) is retained.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 515 (PDF p. 17), Proof of Theorem 22, https://jmlr.org/papers/v2/bousquet02a.html

import Mathlib
import Definitions.Def_StabGen_RKHS_Regularization
import Definitions.Def_FoundationsML_Stability_IsRKHSOf

namespace StabGen.RKHS

open FoundationsML.Stability

/-- Proof of Theorem 22, p. 515: the RKHS distance between the two minimizers. -/
theorem norm_bound {X Y H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {m : ℕ}
    (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ)
    (c : ℝ → Y → ℝ) (σ κ lam : ℝ) (S : Fin m → X × Y)
    (i : Fin m) (f f' : H)
    (hRKHS : IsRKHSOf K Φ ev) (hK : ∀ x : X, K x x ≤ κ ^ 2)
    (hκ : 0 ≤ κ) (hσ : SigmaAdmissible (Set.range ev) c σ) (hlam : 0 < lam)
    (hmin : ∀ g : H, regRisk c ev S lam (fun h : H => ‖h‖ ^ 2) f ≤
      regRisk c ev S lam (fun h : H => ‖h‖ ^ 2) g)
    (hmin' : ∀ g : H, truncRegRisk c ev S i lam (fun h : H => ‖h‖ ^ 2) f' ≤
      truncRegRisk c ev S i lam (fun h : H => ‖h‖ ^ 2) g) :
    ‖f' - f‖ ≤ κ * σ / (2 * lam * (m : ℝ)) := by sorry

end StabGen.RKHS
