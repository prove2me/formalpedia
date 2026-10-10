-- Prove2me | Theorems.Thm_ProxADMMLC_Conv_eq_3_5
-- name    : ProxADMMLC.Conv.eq_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:47.249998+00:00
-- url     : https://prove2.me/theorems/e45f19a8-32a2-46f3-984f-03a2fbd1b947
-- title:
--   (3.5), p. 2279 — φᵗ ≥ M(zᵗ) ≥ f̲: the potential is bounded below
-- statement:
--   Let $f$ be differentiable and $p>0$, let $x(y,z)$, $d$, $x^*(z)$, $M$ be as in (2.6)–(2.9), and let $\underline f=\min_{x\in P,\,Ax=b}f(x)$. Then $M(z)\ge\underline f$ for every $z\in P$, and for every run $(x^t,y^t,z^t)$ of Algorithm 2.2 (with any parameters) and every $t$, the potential $\phi^t=K(x^t,z^t;y^t)-2d(y^t,z^t)+2M(z^t)$ satisfies
--   $$\phi^t\ \ge\ M(z^t)\ \ge\ \underline f.\tag{3.5}$$
--
--   Since the potential decreases by (3.37), this lower bound makes the decreases summable; it is also what bounds the iteration count in Theorem 4.2.
--
--   **Formalization Note** $\underline f$ is `sInf (f '' feas A b ℓ u)`. The feasible set is nonempty (it contains $x^*(z)$) and compact, and $f$ is continuous, so the infimum is attained and equals the paper's minimum; it is never Lean's junk value of `sInf` on an empty or unbounded set.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), p. 2279, (3.5) and the definition of f̲ (§3.1.1)

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

namespace ProxADMMLC.Conv

theorem eq_3_5 {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (hdiff : Differentiable ℝ f) (Γ p c α β : ℝ)
    (hp : 0 < p) (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs)
    (xst : E n → E n) (hxst : IsXStarSel f A b ℓ u p xst)
    (x z : ℕ → E n) (y : ℕ → E m) (hrun : IsRun f A b ℓ u Γ p c α β x y z) :
    (∀ w ∈ box ℓ u, sInf (f '' feas A b ℓ u) ≤ Mval f p xst w) ∧
      ∀ t, Mval f p xst (z t) ≤ phi f A b Γ p xs xst (x t) (z t) (y t) ∧
        sInf (f '' feas A b ℓ u) ≤ Mval f p xst (z t) := by sorry

end ProxADMMLC.Conv
