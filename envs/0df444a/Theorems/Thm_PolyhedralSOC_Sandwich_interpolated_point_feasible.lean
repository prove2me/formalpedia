-- Prove2me | Theorems.Thm_PolyhedralSOC_Sandwich_interpolated_point_feasible
-- name    : PolyhedralSOC.Sandwich.interpolated_point_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:53:06.402634+00:00
-- url     : https://prove2.me/theorems/49a5cf1b-dde8-4a44-b785-48dbede2ed13
-- title:
--   Proof of Proposition 4.1 — the point x_δ = (1−δ)y + δx̄ is feasible for (CQP)
-- statement:
--   Let (CQP) be a conic quadratic problem, let $\bar x$ be strictly feasible with margin $r>0$ (hypothesis (i) of Proposition 4.1), let $\varepsilon>0$, and let $y$ be feasible for (CQP$_\varepsilon$). Put $t_\ell=c_\ell^Ty-d_\ell$ for $\ell=1,\dots,m$. If $\delta\in[0,1]$ satisfies
--   $$
--   \delta\ \ge\ \frac{\varepsilon t_\ell}{r+\varepsilon t_\ell}\qquad\text{for every }\ell=1,\dots,m,
--   $$
--   then the point $x_\delta=(1-\delta)y+\delta\bar x$ is feasible for (CQP), i.e. $Ax_\delta\ge b$ and $\|A_\ell x_\delta-b_\ell\|_2\le c_\ell^Tx_\delta-d_\ell$ for every $\ell$.
--
--   In particular this holds for the paper's choice $\delta=\max_\ell \varepsilon t_\ell/(r+\varepsilon t_\ell)$. It is the step of the proof of Proposition 4.1 that moves a relaxed-feasible point towards the strictly feasible point until it becomes feasible.
--
--   **Formalization Note** The statement is given for every $\delta\in[0,1]$ dominating all the ratios rather than only for their maximum; this contains the paper's case (the maximum lies in $[0,1)$ because $t_\ell\ge0$) and avoids a maximum over an empty index set when $m=0$.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 203 (PDF 11), proof of Proposition 4.1

import Mathlib
import Definitions.Def_PolyhedralSOC_Sandwich_CQP
import Definitions.Def_PolyhedralSOC_Sandwich_Conditions

open Matrix

namespace PolyhedralSOC.Sandwich

/-- Proof of Proposition 4.1, p. 203 (PDF p. 11) (Ben-Tal & Nemirovski, *On Polyhedral
Approximations of the Second-Order Cone*, Math. Oper. Res. 26(2):193–205 (2001)):
let `x̄` be strictly feasible for (CQP) with margin `r > 0` (hypothesis (i)), let `y` be
feasible for (CQP_ε), `ε > 0`, and put `t_ℓ = c_ℓᵀy − d_ℓ`. For every `δ ∈ [0, 1]` with
`δ ≥ ε t_ℓ / (r + ε t_ℓ)` for all `ℓ` (in particular for the paper's
`δ = max_ℓ ε t_ℓ / (r + ε t_ℓ)`), the point `x_δ = (1 − δ) y + δ x̄` is feasible for (CQP). -/
theorem interpolated_point_feasible {n k₀ m : ℕ} (P : CQP n k₀ m)
    (xbar : Fin n → ℝ) (r : ℝ) (hi : IsStrictlyFeasible P xbar r)
    (ε : ℝ) (hε : 0 < ε) (y : Fin n → ℝ) (hy : y ∈ feasRelaxed P ε)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδ : ∀ ℓ, ε * (P.c ℓ ⬝ᵥ y - P.d ℓ) / (r + ε * (P.c ℓ ⬝ᵥ y - P.d ℓ)) ≤ δ) :
    (1 - δ) • y + δ • xbar ∈ feas P := by sorry

end PolyhedralSOC.Sandwich
