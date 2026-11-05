-- Prove2me | Theorems.Thm_StrongConv_supp_subset_Icc_of_extends_nu_one
-- name    : StrongConv.supp_subset_Icc_of_extends_nu_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:58:02.33543+00:00
-- url     : https://prove2.me/theorems/4980c6fd-5193-429b-8fa0-422d8b2bc6fa
-- title:
--   Corollary 9.7 — supp ν₁ ⊆ [−‖P(s, s*)‖, ‖P(s, s*)‖]
-- statement:
--   Let $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ be self-adjoint. If $\mu$ is a compactly supported distribution (Definition 4.6) that agrees on real polynomials with the first-order coefficient $\nu_1$ of the expansion of $\mathbf E[\mathrm{tr}_{DN}\, h(P(\boldsymbol S^N, \boldsymbol S^{N*}))]$ in powers of $1/N$ (`nu P 1`), then $\operatorname{supp}\mu \subseteq [-\|P(\boldsymbol s, \boldsymbol s^*)\|, \|P(\boldsymbol s, \boldsymbol s^*)\|]$. The paper's $\nu_1$ is the distribution of Theorem 7.1, the unique extension (Lemma 4.7); the statement is phrased for every extension. The section fixes $P$ "as in Theorem 3.9" ($d \ge 2$, degree $q_0$); the statement keeps only self-adjointness.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 29, Corollary 9.7

import Mathlib
import Definitions.Def_StrongConv

open Polynomial

namespace StrongConv

theorem supp_subset_Icc_of_extends_nu_one {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    (μ : smoothFun →ₗ[ℝ] ℝ) (hμ : IsCSDistribution μ)
    (hext : ∀ h : ℝ[X], μ (polyFun h) = nu P 1 h) :
    supp μ ⊆ Set.Icc (-‖P.eval (sLimit d)‖) ‖P.eval (sLimit d)‖ := by
  sorry

end StrongConv
