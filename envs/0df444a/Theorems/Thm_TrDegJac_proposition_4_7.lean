-- Prove2me | Theorems.Thm_TrDegJac_proposition_4_7
-- name    : TrDegJac.proposition_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:18.659808+00:00
-- url     : https://prove2.me/theorems/34d9c1b7-a16c-4650-9fd9-a7612db9c1c9
-- title:
--   Proposition 4.7 — $\operatorname{rank}_{\mathbb F(x)}\mathrm{Jac}(f)\le\operatorname{tr-deg}_{\mathbb F}(f)$ over every field
-- statement:
--   Let $\mathbb F$ be any field and $f_1,\dots,f_m\in\mathbb F[x_1,\dots,x_n]$. Then
--   $$
--   \operatorname{rank}_{\mathbb F(x)}\mathrm{Jac}_x(f)\ \le\ \operatorname{tr-deg}_{\mathbb F}(f).
--   $$
--
--   This is the easy half of the Jacobian criterion, valid in every characteristic, and the upper clause of the mission's goal.
--
--   Differences from the source: none.
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), Proposition 4.7, p.27

import Mathlib
import Definitions.Def_TrDegJac_trDeg
import Definitions.Def_TrDegJac_jacobian

set_option autoImplicit false

namespace TrDegJac

/-- **Proposition 4.7** — Forbes and Staicu, *Approximating Transcendence Degree in Medium Characteristic*, STOC 2027
submission (manuscript sha256 3ab72a42…), p.27:
"Let F be any field and f₁, …, f_m ∈ F[x₁, …, x_n] then rank_{F(x)} Jac(f) ≤ tr-deg_F(f)."

**Formalization Note.** `jacobian f` is the `n × m` Jacobian with entries in `F(x)`, and its
`Matrix.rank` is the rank over `F(x)`; `trDeg f` is the maximum size of an algebraically independent
subfamily (Definition 2.5). -/
theorem proposition_4_7 {F : Type*} [Field F] {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) F) :
    (jacobian f).rank ≤ trDeg f := by sorry

end TrDegJac
