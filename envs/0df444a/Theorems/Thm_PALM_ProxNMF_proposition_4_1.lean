-- Prove2me | Theorems.Thm_PALM_ProxNMF_proposition_4_1
-- name    : PALM.ProxNMF.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:09:25.781094+00:00
-- url     : https://prove2.me/theorems/7856144c-279c-4f4e-a9ee-e60281afd336
-- title:
--   Proposition 4.1 (Proximal map formula) — $\mathrm{prox}^f_1(U)=T_s(P_+(U))$ for $f=\delta_{X\ge0}+\delta_{\|X\|_0\le s}$
-- statement:
--   Let $U\in\mathbb R^{m\times n}$, let $s$ be a natural number, and let $f:=\delta_{X\ge0}+\delta_{\|X\|_0\le s}$, the indicator of the nonnegative matrices with at most $s$ nonzero entries. Then
--
--   $$\operatorname{prox}^f_1(U)=\operatorname{argmin}\Big\{\frac12\|X-U\|_F^2 : X\ge0,\ \|X\|_0\le s\Big\}=T_s\big(P_+(U)\big),$$
--
--   where $\operatorname{prox}^f_1$ is the proximal map (2.2) with $t=1$, $T_s$ is the hard-thresholding operator of Definition 4.1, and $P_+(U)=\max\{0,U\}$ componentwise. All three sides are sets, and both equalities are equalities of sets.
--
--   This formula is what makes PALM implementable for sparse nonnegative matrix factorization: the proximal step for the nonconvex constraint reduces to clipping the negative entries of $U$ and then keeping $s$ largest entries.
--
--   **Formalization Note** Matrices are `Matrix (Fin m) (Fin n) ℝ`. $f$ takes values in `EReal`, so membership in $\operatorname{prox}^f_1(U)$ is the inequality $f(X)+\frac12\|X-U\|_F^2\le f(W)+\frac12\|W-U\|_F^2$ in `EReal` for every $W$. No restriction is placed on $s$: $s=0$ and $s\ge mn$ are included.
-- source:
--   Bolte, Sabach, Teboulle, Proximal alternating linearized minimization for nonconvex and nonsmooth problems, Math. Program. 146 (2014), doi:10.1007/s10107-013-0701-9 (source: author version), p. 28, Proposition 4.1

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_PALM_ProxNMF_Setting

open CaiCandesShen.ProximalLimit PALM.ProxNMF

namespace PALM.ProxNMF

/-- Proposition 4.1 (Proximal map formula), p. 28: for `f := δ_{X≥0} + δ_{‖X‖₀≤s}`,
`prox^f_1(U) = argmin {½‖X − U‖²_F : X ≥ 0, ‖X‖₀ ≤ s} = T_s(P_+(U))`, as sets. -/
theorem proposition_4_1 {m n : ℕ} (s : ℕ) (U : Matrix (Fin m) (Fin n) ℝ) :
    proxSet (f s) 1 U =
        argminOn (fun X => 1 / 2 * frobInner (X - U) (X - U))
          {X | X ∈ NonnegSet m n ∧ l0 X ≤ s} ∧
      argminOn (fun X => 1 / 2 * frobInner (X - U) (X - U))
          {X | X ∈ NonnegSet m n ∧ l0 X ≤ s} =
        Ts s (Pplus U) := by sorry

end PALM.ProxNMF
