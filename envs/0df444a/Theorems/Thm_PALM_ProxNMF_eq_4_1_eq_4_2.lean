-- Prove2me | Theorems.Thm_PALM_ProxNMF_eq_4_1_eq_4_2
-- name    : PALM.ProxNMF.eq_4_1_eq_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:09:06.460295+00:00
-- url     : https://prove2.me/theorems/3fce7995-8c48-471e-848e-891e967b4fd7
-- title:
--   Proof of Proposition 4.1, (4.1) = (4.2) — the negative-index entries of a minimizer vanish
-- statement:
--   Fix $U\in\mathbb R^{m\times n}$ and $s\in\mathbb N$, with $\mathcal I^\pm$ and $\|\cdot\|_\pm^2$ as in the setting. The two minimizer sets
--
--   $$\operatorname{argmin}\Big\{\|X-U\|_+^2+\|X\|_-^2-2\sum_{(i,j)\in\mathcal I^-}X_{ij}U_{ij} : X\ge0,\ \|X\|_0\le s\Big\}\qquad(4.1)$$
--
--   and
--
--   $$\operatorname{argmin}\big\{\|X-U\|_+^2 : X_{ij}=0\ \forall (i,j)\in\mathcal I^-,\ X\ge0,\ \|X\|_0\le s\big\}\qquad(4.2)$$
--
--   are equal.
--
--   In the proof of Proposition 4.1, the objective of (4.1) is $\|X-U\|_F^2$ minus the constant $\|U\|_-^2$, so this step shows that a nonnegative sparse projection of $U$ vanishes where $U$ is negative.
--
--   **Formalization Note** Both sides are sets of minimizers (possibly with several elements), not chosen points. The objective of (4.1) is written exactly as printed, without the constant $\|U\|_-^2$.
-- source:
--   Bolte, Sabach, Teboulle, Proximal alternating linearized minimization for nonconvex and nonsmooth problems, Math. Program. 146 (2014), doi:10.1007/s10107-013-0701-9 (source: author version), p. 29, §4.2, proof of Proposition 4.1, (4.1)–(4.2)

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_PALM_ProxNMF_Setting

open CaiCandesShen.ProximalLimit PALM.ProxNMF

namespace PALM.ProxNMF

/-- (4.1) = (4.2), proof of Proposition 4.1 (p. 29): the argmin of
`‖X − U‖²_+ + ‖X‖²_− − 2 ∑_{I⁻} X_ij U_ij` over `X ≥ 0, ‖X‖₀ ≤ s` equals the argmin of
`‖X − U‖²_+` over `X_ij = 0 ∀ (i, j) ∈ I⁻, X ≥ 0, ‖X‖₀ ≤ s`. -/
theorem eq_4_1_eq_4_2 {m n : ℕ} (s : ℕ) (U : Matrix (Fin m) (Fin n) ℝ) :
    argminOn
        (fun X => normSqPlus U (X - U) + normSqMinus U X
          - 2 * ∑ p ∈ Iminus U, X p.1 p.2 * U p.1 p.2)
        {X | X ∈ NonnegSet m n ∧ l0 X ≤ s} =
      argminOn (fun X => normSqPlus U (X - U))
        {X | (∀ p ∈ Iminus U, X p.1 p.2 = 0) ∧ X ∈ NonnegSet m n ∧ l0 X ≤ s} := by sorry

end PALM.ProxNMF
