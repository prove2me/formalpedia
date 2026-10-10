-- Prove2me | Theorems.Thm_QCQPTightness_MultTight_theorem_8
-- name    : QCQPTightness.MultTight.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:10.520788+00:00
-- url     : https://prove2.me/theorems/cc902ff4-bb2d-41a9-84e9-34b112306cd4
-- title:
--   Theorem 8, p. 30 — if the quadratic eigenvalue multiplicity satisfies k ≥ m + 1, then conv(𝒟 ∩ H) = 𝒟_SDP ∩ H and Opt = Opt_SDP
-- statement:
--   Consider a QCQP $\inf\{q_0(x) : q_i(x)\le 0\ (i\in[\![m_I]\!]),\ q_i(x)=0\ (i\in[\![m_I+1,m]\!])\}$ with $m\ge 1$ constraints, epigraph $\mathcal D$, and Shor SDP relaxation with optimal value $\mathrm{Opt}_{\mathrm{SDP}}$ and projected epigraph $\mathcal D_{\mathrm{SDP}}$. Suppose Assumption 1 holds: the QCQP is feasible and some $\gamma^*$ with $\gamma^*_i\ge 0$ on the inequality constraints has $A_0+\sum_i\gamma^*_iA_i\succ 0$. Define the hyperplane
--
--   $$H = \{(x,t)\in\mathbb R^{N+1} : 2t = \mathrm{Opt}_{\mathrm{SDP}}\}.$$
--
--   If the quadratic eigenvalue multiplicity $k$ of the QCQP (Definition 3) satisfies $k\ge m+1$, then
--
--   $$\operatorname{conv}(\mathcal D\cap H) = \mathcal D_{\mathrm{SDP}}\cap H\qquad\text{and}\qquad \mathrm{Opt}=\mathrm{Opt}_{\mathrm{SDP}}.$$
--
--   The theorem says that, with one copy of symmetry fewer than Theorem 7 requires, the SDP relaxation is still exact in value and its optimal face is the convex hull of the QCQP's optimal epigraph points.
--
--   **Formalization Note** $\mathrm{Opt}$ and $\mathrm{Opt}_{\mathrm{SDP}}$ are `EReal` infima, and $H$ is defined from the `EReal` value, so the value identity is stated as a separate conjunct. The quadratic eigenvalue multiplicity is the largest $k$ (`IsGreatest`), as in Definition 3. Constraints are indexed by `Fin m` with inequalities first.
-- source:
--   arXiv:1911.09195v3, Theorem 8, p. 30 (restated and proved in App. B, pp. 35–36)

import Mathlib
import Definitions.Def_QCQPTightness_MultTight_QCQP
import Definitions.Def_QCQPTightness_MultTight_Mult
import Definitions.Def_QCQPTightness_MultTight_Kron

namespace QCQPTightness.MultTight

open QCQP Matrix

/-- Theorem 8 (arXiv:1911.09195v3, p. 30; restated p. 35): under Assumption 1, with
`H = {(x, t) : 2t = Opt_SDP}`, if the quadratic eigenvalue multiplicity `k` satisfies
`k ≥ m + 1`, then `conv(𝒟 ∩ H) = 𝒟_SDP ∩ H`, and `Opt = Opt_SDP`. -/
theorem theorem_8 {N m : ℕ} (P : QCQP N m) (hm : 1 ≤ m) (h1 : P.Assumption1)
    (k : ℕ) (hk : P.IsQuadEigMult k) (hkm : m + 1 ≤ k) :
    convexHull ℝ (P.D ∩ P.hyperplaneH) = P.DSDP ∩ P.hyperplaneH ∧ P.Opt = P.OptSDP := by sorry

end QCQPTightness.MultTight
