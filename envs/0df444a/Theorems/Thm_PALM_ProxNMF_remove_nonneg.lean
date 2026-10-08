-- Prove2me | Theorems.Thm_PALM_ProxNMF_remove_nonneg
-- name    : PALM.ProxNMF.remove_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:08:49.303433+00:00
-- url     : https://prove2.me/theorems/81b630d4-f747-497c-9b68-5888e387f98a
-- title:
--   Proof of Proposition 4.1 — the constraint $X\ge 0$ in problem (4.2) can be removed
-- statement:
--   Fix $U\in\mathbb R^{m\times n}$ and $s\in\mathbb N$, with $\mathcal I^-=\{(i,j):U_{ij}<0\}$ and $\|\cdot\|_+^2$ as in the setting. Then
--
--   $$\operatorname{argmin}\big\{\|X-U\|_+^2 : X_{ij}=0\ \forall (i,j)\in\mathcal I^-,\ X\ge0,\ \|X\|_0\le s\big\}
--   =\operatorname{argmin}\big\{\|X-U\|_+^2 : X_{ij}=0\ \forall (i,j)\in\mathcal I^-,\ \|X\|_0\le s\big\}.$$
--
--   That is, dropping the nonnegativity constraint from problem (4.2) does not change its set of optimal solutions. Together with relations (ii) and (iii) this turns (4.2) into a hard-thresholding problem for $P_+(U)$ without sign constraints.
-- source:
--   Bolte, Sabach, Teboulle, Proximal alternating linearized minimization for nonconvex and nonsmooth problems, Math. Program. 146 (2014), doi:10.1007/s10107-013-0701-9 (source: author version), p. 29, §4.2, proof of Proposition 4.1 (unnumbered sentence after (4.2))

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_PALM_ProxNMF_Setting

open CaiCandesShen.ProximalLimit PALM.ProxNMF

namespace PALM.ProxNMF

/-- Proof of Proposition 4.1 (p. 29): the constraint `X ≥ 0` in problem (4.2) can be removed
without affecting its set of optimal solutions. -/
theorem remove_nonneg {m n : ℕ} (s : ℕ) (U : Matrix (Fin m) (Fin n) ℝ) :
    argminOn (fun X => normSqPlus U (X - U))
        {X | (∀ p ∈ Iminus U, X p.1 p.2 = 0) ∧ X ∈ NonnegSet m n ∧ l0 X ≤ s} =
      argminOn (fun X => normSqPlus U (X - U))
        {X | (∀ p ∈ Iminus U, X p.1 p.2 = 0) ∧ l0 X ≤ s} := by sorry

end PALM.ProxNMF
