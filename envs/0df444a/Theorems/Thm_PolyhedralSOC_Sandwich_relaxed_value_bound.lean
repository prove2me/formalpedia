-- Prove2me | Theorems.Thm_PolyhedralSOC_Sandwich_relaxed_value_bound
-- name    : PolyhedralSOC.Sandwich.relaxed_value_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:53:45.025983+00:00
-- url     : https://prove2.me/theorems/457ab393-e0bb-4d93-abeb-4e87b28b7b77
-- title:
--   Proof of Proposition 4.1 — semiboundedness gives (1−δ)t_ℓ ≤ R
-- statement:
--   Let (CQP) be a conic quadratic problem, let $\bar x$ be strictly feasible with margin $r>0$ (hypothesis (i) of Proposition 4.1), and let (CQP) be semibounded with bound $R$ (hypothesis (ii)). Let $\varepsilon>0$, let $y$ be feasible for (CQP$_\varepsilon$), put $t_\ell=c_\ell^Ty-d_\ell$, and let $\delta\in[0,1]$ satisfy $\delta\ge\varepsilon t_\ell/(r+\varepsilon t_\ell)$ for every $\ell$. Then
--   $$
--   (1-\delta)\,t_\ell\ \le\ R\qquad\text{for all }\ell=1,\dots,m.
--   $$
--
--   In the paper this follows from applying (ii) to the feasible point $x_\delta=(1-\delta)y+\delta\bar x$, which gives $\delta[c_\ell^T\bar x-d_\ell]+(1-\delta)t_\ell\le R$, together with $c_\ell^T\bar x-d_\ell\ge0$.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 203 (PDF 11), proof of Proposition 4.1

import Mathlib
import Definitions.Def_PolyhedralSOC_Sandwich_CQP
import Definitions.Def_PolyhedralSOC_Sandwich_Conditions

open Matrix

namespace PolyhedralSOC.Sandwich

/-- Proof of Proposition 4.1, p. 203 (PDF p. 11) (Ben-Tal & Nemirovski, *On Polyhedral
Approximations of the Second-Order Cone*, Math. Oper. Res. 26(2):193–205 (2001)):
under (i) (strict feasibility of `x̄` with margin `r`) and (ii) (semiboundedness with bound
`R`), for `y` feasible for (CQP_ε), `ε > 0`, `t_ℓ = c_ℓᵀy − d_ℓ`, and `δ ∈ [0, 1]` with
`δ ≥ ε t_ℓ / (r + ε t_ℓ)` for all `ℓ`, one has `(1 − δ) t_ℓ ≤ R` for all `ℓ`
("It follows from (ii) that [c_ℓᵀx_δ − d_ℓ] = δ[c_ℓᵀx̄ − d_ℓ] + (1 − δ)t_ℓ ≤ R … whence
(1 − δ)t_ℓ ≤ R for all ℓ"). -/
theorem relaxed_value_bound {n k₀ m : ℕ} (P : CQP n k₀ m)
    (xbar : Fin n → ℝ) (r : ℝ) (hi : IsStrictlyFeasible P xbar r)
    (R : ℝ) (hii : IsSemibounded P R)
    (ε : ℝ) (hε : 0 < ε) (y : Fin n → ℝ) (hy : y ∈ feasRelaxed P ε)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδ : ∀ ℓ, ε * (P.c ℓ ⬝ᵥ y - P.d ℓ) / (r + ε * (P.c ℓ ⬝ᵥ y - P.d ℓ)) ≤ δ) :
    ∀ ℓ, (1 - δ) * (P.c ℓ ⬝ᵥ y - P.d ℓ) ≤ R := by sorry

end PolyhedralSOC.Sandwich
