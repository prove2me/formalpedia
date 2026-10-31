-- Prove2me | Theorems.Thm_PriceRobust_Stability_cost_projection_unique_nonneg
-- name    : PriceRobust.Stability.cost_projection_unique_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:10.315771+00:00
-- url     : https://prove2.me/theorems/acae598e-67c4-4d7a-b8ff-8c2136367609
-- title:
--   Proof of Theorem 2, (12)–(15), pp. 13–14 — the projection LCP has a unique solution w′ = Θ(w), and w′ ≥ 0
-- statement:
--   Consider the market of §3 with $a\ge 0$ and Assumptions (P), (Z), (IS), and fix $w\in\mathbb R^{\mathcal N}_{++}$. With $Q(w')=\Psi(R)a-\Psi(R)Rw'$, the linear complementarity problem
--   $$w'\le w,\qquad Q(w')^\top(w-w')=0,\qquad Q(w')\ge 0$$
--   has exactly one solution $w'=\Theta(w)$, and every solution satisfies $w'\ge 0$.
--
--   This is the step of the proof of Theorem 2 that makes the special equilibrium $(p^*|w)=p^*(\Theta(w))$ well defined. The paper obtains it from Federgruen and Hu (2015): uniqueness from the positive definiteness of $\Psi(R)R$ (their Proposition 2(d)), and $w'\ge 0$ from property (NPW), which holds under (IS) (their Proposition 3). Those facts are not proved in this paper.
-- source:
--   Federgruen & Hu, Global robust stability in a general price and assortment competition model, submitted manuscript (TSpace / SSRN 3010503), pp. 13–14 (PDF 14–15), proof of Theorem 2, eqs. (12)–(15)

import Mathlib
import Definitions.Def_PriceRobust_Stability_Model

open Matrix

namespace PriceRobust.Stability

theorem cost_projection_unique_nonneg {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (M : Market ι F) (hM : M.Standing) (w : ι → ℝ) (hw : ∀ l, 0 < w l) :
    (∃! w' : ι → ℝ, M.IsCostProjection w w') ∧
      ∀ w' : ι → ℝ, M.IsCostProjection w w' → 0 ≤ w' := by sorry

end PriceRobust.Stability
