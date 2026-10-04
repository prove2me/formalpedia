-- Prove2me | Theorems.Thm_StabGen_RKHS_rkhs_regularization_uniform_stability
-- name    : StabGen.RKHS.rkhs_regularization_uniform_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:56:38.962997+00:00
-- url     : https://prove2.me/theorems/9c282807-9dc7-43c2-8d65-73345bf145c4
-- title:
--   Theorem 22 — RKHS regularization stability
-- statement:
--   Let $H$ be a real RKHS with kernel $K$ satisfying $K(x,x)\le\kappa^2$ for every $x$. Let the loss $\ell(f,(x,y))=c(f(x),y)$ be $\sigma$-admissible, and fix $\lambda>0$. Given any sample $S=(z_1,\ldots,z_m)$ and index $i$, let $f$ minimize (19) over $H$ with $N(g)=\|g\|_K^2$, and let $f^{\setminus i}$ minimize (20) over $H$ with the same regularizer. Then for every test point $z$,
--   $$|\ell(f,z)-\ell(f^{\setminus i},z)|\le\frac{\sigma^2\kappa^2}{2\lambda m}.$$
--
--   This yields the deletion-based stability estimate underlying Theorem 22. The related replace-one estimate in Mohri, Rostamizadeh and Talwalkar has twice this constant.
--
--   **Formalization Note** The printed theorem calls $f^{\setminus i}$ the algorithm run on $S^{\setminus i}$ using (26), but its proof compares (19) with (20), whose data term retains $1/m$. This statement follows that proof. Running (26) literally on $m-1$ points instead uses $1/(m-1)$ and is not the asserted pairwise comparison. The squared constant makes the sign of $\kappa$ immaterial here.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), pp. 514–515 (PDF pp. 16–17), Theorem 22 and proof, https://jmlr.org/papers/v2/bousquet02a.html

import Mathlib
import Definitions.Def_StabGen_RKHS_Regularization
import Definitions.Def_FoundationsML_Stability_IsRKHSOf

namespace StabGen.RKHS

open FoundationsML.Stability

/-- Theorem 22, p. 514, in the pairwise form established by its proof:
the second minimizer uses the `1/m` truncated objective (20). -/
theorem rkhs_regularization_uniform_stability {X Y H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {m : ℕ} (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ)
    (c : ℝ → Y → ℝ) (σ κ lam : ℝ) (S : Fin m → X × Y)
    (i : Fin m) (f f' : H)
    (hRKHS : IsRKHSOf K Φ ev) (hK : ∀ x : X, K x x ≤ κ ^ 2)
    (hσ : SigmaAdmissible (Set.range ev) c σ) (hlam : 0 < lam)
    (hmin : ∀ g : H, regRisk c ev S lam (fun h : H => ‖h‖ ^ 2) f ≤
      regRisk c ev S lam (fun h : H => ‖h‖ ^ 2) g)
    (hmin' : ∀ g : H, truncRegRisk c ev S i lam (fun h : H => ‖h‖ ^ 2) f' ≤
      truncRegRisk c ev S i lam (fun h : H => ‖h‖ ^ 2) g) :
    ∀ z : X × Y,
      |Loss c (ev f) z - Loss c (ev f') z| ≤
        σ ^ 2 * κ ^ 2 / (2 * lam * (m : ℝ)) := by sorry

end StabGen.RKHS
