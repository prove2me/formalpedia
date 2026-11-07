-- Prove2me | Theorems.Thm_StrongConv_norm_toFull_eq_fullNorm
-- name    : StrongConv.norm_toFull_eq_fullNorm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T08:50:57.091641+00:00
-- url     : https://prove2.me/theorems/a218499e-a461-4854-b2dc-d7792e11d448
-- title:
--   Choi, Theorem 7 — the norm of P(u, u*) in M_D(ℂ) ⊗ C*(F_d) is the supremum of ‖P(U, U*)‖ over unitary matrices
-- statement:
--   Let $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ be a noncommutative polynomial in $d$ variables with $D \times D$ matrix coefficients (`StrongConv.NCPoly D d`). Then the norm of $P(\boldsymbol u, \boldsymbol u^*) = \sum_w A_w \otimes w(\boldsymbol u, \boldsymbol u^*)$ in the $C^*$-algebra $\mathrm M_D(C^*(\mathbf F_d))$, where $u_1, \dots, u_d$ are the canonical unitaries of the full group $C^*$-algebra of the free group, not the paper's left-regular $s_i$ (`StrongConv.NCPoly.toFull P`, an element of `CStarMatrix (Fin D) (Fin D) (FullGroupCStar (FreeGroup (Fin d)))`), equals the paper's
--   $$\|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)} = \sup_{\boldsymbol U} \|P(\boldsymbol U, \boldsymbol U^*)\|,$$
--   the supremum over all $d$-tuples $\boldsymbol U$ of $n \times n$ unitary matrices, for all $n \ge 0$ (`StrongConv.NCPoly.fullNorm`).
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 12, the identification of ‖P‖_{M_D(ℂ)⊗C*(F_d)} with the norm of P(s, s*) in M_D(C*(F_d)), which cites Choi, M. D., The full C*-algebra of the free group on two generators, Pacific J. Math. 87 (1980) 41–48, https://doi.org/10.2140/pjm.1980.87.41, Theorem 7 (p. 45)

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_FullGroupCStar
import Definitions.Def_StrongConvFull

namespace StrongConv

theorem norm_toFull_eq_fullNorm {D d : ℕ} (P : NCPoly D d) : ‖P.toFull‖ = P.fullNorm := by
  sorry

end StrongConv
