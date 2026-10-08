-- Prove2me | Theorems.Thm_PALM_ProxNMF_facts_i_ii_iii
-- name    : PALM.ProxNMF.facts_i_ii_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:08:55.394915+00:00
-- url     : https://prove2.me/theorems/880d254f-3479-405d-a930-aeb75f39ab8d
-- title:
--   Proof of Proposition 4.1, relations (i)–(iii) — $\|X\|_F^2=\|X\|_+^2+\|X\|_-^2$, $\|X-U\|_+^2+\|X\|_-^2=\|X-P_+(U)\|_F^2$
-- statement:
--   Fix $U\in\mathbb R^{m\times n}$ and let $\mathcal I^+=\{(i,j):U_{ij}\ge0\}$, $\mathcal I^-=\{(i,j):U_{ij}<0\}$, $\|X\|_\pm^2=\sum_{(i,j)\in\mathcal I^\pm}X_{ij}^2$, and $P_+(U)=\max\{0,U\}$ componentwise. Then for every $X\in\mathbb R^{m\times n}$:
--
--   1. $$\|X\|_F^2=\|X\|_+^2+\|X\|_-^2;$$
--   2. $$\|X-U\|_+^2+\|X\|_-^2=\|X-P_+(U)\|_F^2;$$
--   3. $\|X\|_-^2=0$ if and only if $X_{ij}=0$ for all $(i,j)\in\mathcal I^-$.
--
--   These identities convert the constrained proximal problem of Proposition 4.1 into a hard-thresholding problem for $P_+(U)$.
-- source:
--   Bolte, Sabach, Teboulle, Proximal alternating linearized minimization for nonconvex and nonsmooth problems, Math. Program. 146 (2014), doi:10.1007/s10107-013-0701-9 (source: author version), pp. 28–29, §4.2, proof of Proposition 4.1, relations (i)–(iii)

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_PALM_ProxNMF_Setting

open CaiCandesShen.ProximalLimit PALM.ProxNMF

namespace PALM.ProxNMF

/-- Relations (i)–(iii) in the proof of Proposition 4.1 (pp. 28–29): for every `X` (with `U` fixed),
(i) `‖X‖²_F = ‖X‖²_+ + ‖X‖²_−`, (ii) `‖X − U‖²_+ + ‖X‖²_− = ‖X − P_+(U)‖²_F`,
(iii) `‖X‖²_− = 0 ⇔ X_ij = 0` for all `(i, j) ∈ I⁻`. -/
theorem facts_i_ii_iii {m n : ℕ} (U X : Matrix (Fin m) (Fin n) ℝ) :
    frobInner X X = normSqPlus U X + normSqMinus U X ∧
    normSqPlus U (X - U) + normSqMinus U X = frobInner (X - Pplus U) (X - Pplus U) ∧
    (normSqMinus U X = 0 ↔ ∀ p ∈ Iminus U, X p.1 p.2 = 0) := by sorry

end PALM.ProxNMF
