-- Prove2me | Theorems.Thm_QCQPTightness_SOCP_proposition_1
-- name    : QCQPTightness.SOCP.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:23:36.855015+00:00
-- url     : https://prove2.me/theorems/c412d1fd-e62a-44e6-a2eb-8606a6c0257c
-- title:
--   Proposition 1, p. 21 — for a diagonal QCQP, 𝒟_SOCP = 𝒟_SDP and Opt_SOCP = Opt_SDP
-- statement:
--   Consider a QCQP (1) with $m \ge 1$ constraints, of which the first $m_I$ are inequalities, in the diagonal form (10): $A_i = \mathrm{Diag}(a_i)$ for vectors $a_0, \dots, a_m \in \mathbb{R}^N$, so $q_i(x) = \langle a_i, x^2\rangle + 2\langle b_i, x\rangle + c_i$. Then the SOCP relaxation (11)–(12) and the SDP relaxation (3)–(4) have the same projected epigraph and the same optimal value:
--
--   $$
--   \mathcal{D}_{\mathrm{SOCP}} = \mathcal{D}_{\mathrm{SDP}} \qquad\text{and}\qquad \mathrm{Opt}_{\mathrm{SOCP}} = \mathrm{Opt}_{\mathrm{SDP}}.
--   $$
--
--   No regularity assumption is made: both values may be $+\infty$ (both relaxations infeasible) or $-\infty$.
--
--   Every SD-QCQP becomes a diagonal QCQP after an invertible change of variables, so the result says that for SD-QCQPs the sufficient conditions for SDP tightness and for the convex-hull identity $\mathrm{conv}(\mathcal{D}) = \mathcal{D}_{\mathrm{SDP}}$ apply verbatim to the much smaller SOCP relaxation. The value identity was first recorded by Locatelli; the set identity is new in the paper.
--
--   **Formalization Note** The paper states Proposition 1 "for any SD-QCQP", but $\mathcal{D}_{\mathrm{SOCP}}$ and $\mathrm{Opt}_{\mathrm{SOCP}}$ are defined only for the diagonal form (10), which §4.2.1 assumes throughout ("In the remainder of this section, we assume that we have already made this change of variables"). The theorem is therefore stated for a QCQP together with vectors $a_0, a_i$ and the hypothesis $A_0 = \mathrm{Diag}(a_0)$, $A_i = \mathrm{Diag}(a_i)$. Optimal values are infima in `EReal`. Constraint $i : \mathrm{Fin}\ m$ is the paper's $i+1$, an inequality iff $i < m_I$.
-- source:
--   arXiv:1911.09195v3, Proposition 1, p. 21 (restated and proved in App. A, pp. 34–35)

import Mathlib
import Definitions.Def_QCQPTightness_SOCP_QCQP
import Definitions.Def_QCQPTightness_SOCP_Relaxation

namespace QCQPTightness.SOCP

open Matrix

/-- Proposition 1, p. 21 (restated p. 34), for the diagonal form (10) of an SD-QCQP that §4.2.1
assumes throughout: `𝒟_SOCP = 𝒟_SDP` and `Opt_SOCP = Opt_SDP`. -/
theorem proposition_1 {N m : ℕ} (P : QCQP N m) (hm : 1 ≤ m)
    (a₀ : Fin N → ℝ) (a : Fin m → Fin N → ℝ) (hdiag : P.IsDiagonalQCQP a₀ a) :
    P.DSOCP a₀ a = P.DSDP ∧ P.OptSOCP a₀ a = P.OptSDP := by sorry

end QCQPTightness.SOCP
