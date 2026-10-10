-- Prove2me | Theorems.Thm_QCQPTightness_Sharp_qcqp13_values
-- name    : QCQPTightness.Sharp.qcqp13_values
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:24:42.809988+00:00
-- url     : https://prove2.me/theorems/7b058de8-df25-47a0-b9ba-a87c110bd6f0
-- title:
--   §4.3, proof of Proposition 2, p. 22 — for (13), sup_{γ∈Γ} q(γ, 0) = −1, Opt_SDP ≤ −1 and Opt = 0
-- statement:
--   For positive integers $n,k$ the QCQP (13) satisfies
--   $$
--   \sup_{\gamma\in\Gamma}q(\gamma,0)=-1,\qquad \mathrm{Opt}_{\mathrm{SDP}}\le-1,\qquad \mathrm{Opt}=0 .
--   $$
--   Hence $\mathrm{Opt}\ne\mathrm{Opt}_{\mathrm{SDP}}$ for (13), the last bullet of Proposition 2.
--
--   **Formalization Note** The paper's constraints $1,\dots,m$ are indexed by `Fin m` (index $i$ is the paper's $i+1$); constraint $i$ is an inequality exactly when $i < m_I$. Hence the paper's $\gamma_1$ is `γ 0`. Optimal values are infima in the extended reals `EReal`.
-- source:
--   arXiv:1911.09195v3, §4.3, proof of Proposition 2, p. 22

import Mathlib
import Definitions.Def_QCQPTightness_Sharp_QCQP
import Definitions.Def_QCQPTightness_Sharp_Mult
import Definitions.Def_QCQPTightness_Sharp_Examples

namespace QCQPTightness.Sharp

/-- §4.3, proof of Proposition 2, p. 22: for the QCQP (13), `sup_{γ∈Γ} q(γ, 0) = −1`,
`Opt_SDP ≤ −1` and `Opt = 0`. -/
theorem qcqp13_values (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (⨆ γ ∈ (qcqp13 n k hn).Gamma, (((qcqp13 n k hn).qγ γ 0 : ℝ) : EReal)) = ((-1 : ℝ) : EReal) ∧
    (qcqp13 n k hn).OptSDP ≤ ((-1 : ℝ) : EReal) ∧
    (qcqp13 n k hn).Opt = ((0 : ℝ) : EReal) := by sorry

end QCQPTightness.Sharp
