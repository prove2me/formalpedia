-- Prove2me | Theorems.Thm_StrongConv_isLUB_fullNorm_and_norm_eval_le_fullNorm
-- name    : StrongConv.isLUB_fullNorm_and_norm_eval_le_fullNorm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T07:54:59.243504+00:00
-- url     : https://prove2.me/theorems/3b0645b4-ca57-4773-8511-8d2467158410
-- title:
--   Choi, Theorem 7 — the unitary-matrix supremum ‖P‖_{M_D(ℂ)⊗C*(F_d)} is the norm of the full C*-algebra
-- statement:
--   Let $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ be a noncommutative polynomial in $d$ variables with $D \times D$ matrix coefficients (`StrongConv.NCPoly D d`), and let $\|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)}$ be the paper's norm (`StrongConv.NCPoly.fullNorm`): the supremum of $\|P(\boldsymbol U, \boldsymbol U^*)\|$ over all $d$-tuples $\boldsymbol U$ of $n \times n$ unitary matrices, for all $n \ge 0$. Then:
--
--   1. that supremum is a genuine least upper bound: the set of values $\|P(\boldsymbol U, \boldsymbol U^*)\|$ is bounded above, so the real supremum is not a junk value; and
--   2. for every complex Hilbert space $H$ (in any universe) and every $d$-tuple $\boldsymbol U = (U_1, \dots, U_d)$ of unitary operators on $H$,
--   $$\|P(\boldsymbol U, \boldsymbol U^*)\| \le \|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)},$$
--   where $P(\boldsymbol U, \boldsymbol U^*)$ acts on $H^D$ (`StrongConv.NCPoly.eval`).
--
--   The reverse inequality holds for the finite-dimensional unitaries by definition, so together the two clauses say that $\|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)}$ is the supremum of $\|P(\boldsymbol U, \boldsymbol U^*)\|$ over all unitary representations of $\mathbf F_d$ on Hilbert spaces, which is the norm of $P$ in $\mathrm M_D(C^*(\mathbf F_d))$, the full group $C^*$-algebra with matrix coefficients. No $C^*$-algebra is constructed: the statement is phrased through the representations that define the full norm.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 12, the identification of ‖P‖_{M_D(ℂ)⊗C*(F_d)} with the norm of the full C*-algebra of the free group, which cites Choi, M. D., The full C*-algebra of the free group on two generators, Pacific J. Math. 87 (1980) 41–48, https://doi.org/10.2140/pjm.1980.87.41, Theorem 7 (p. 45)

import Definitions.Def_StrongConv

universe u

namespace StrongConv

theorem isLUB_fullNorm_and_norm_eval_le_fullNorm {D d : ℕ} (P : NCPoly D d) :
    IsLUB {x | ∃ (n : ℕ) (U : Fin d → Matrix.unitaryGroup (Fin n) ℂ),
        x = ‖P.eval (fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (U i : Matrix (Fin n) (Fin n) ℂ))‖}
      P.fullNorm ∧
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (U : Fin d → H →L[ℂ] H), (∀ i, U i ∈ unitary (H →L[ℂ] H)) → ‖P.eval U‖ ≤ P.fullNorm := by
  sorry

end StrongConv
