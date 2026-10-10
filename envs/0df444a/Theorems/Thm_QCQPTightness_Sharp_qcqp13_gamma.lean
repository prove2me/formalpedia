-- Prove2me | Theorems.Thm_QCQPTightness_Sharp_qcqp13_gamma
-- name    : QCQPTightness.Sharp.qcqp13_gamma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:24:13.082528+00:00
-- url     : https://prove2.me/theorems/3316a8c4-6b6d-4f80-88b0-a38ab8226638
-- title:
--   §4.3, proof of Proposition 2, p. 22 — Γ = {γ : γ₁ ≥ 1} for (13), so Assumption 3 holds
-- statement:
--   For positive integers $n,k$, the dual set of the QCQP (13) is the halfspace
--   $$
--   \Gamma=\{\gamma\in\mathbb R^{m} : \gamma_1\ge0,\ A(\gamma)\succeq0\}=\{\gamma\in\mathbb R^m : \gamma_1\ge1\},
--   $$
--   and in particular $\Gamma$ is polyhedral (Assumption 3).
--
--   Its only semidefinite face is therefore the hyperplane $\{\gamma_1=1\}$.
--
--   **Formalization Note** The paper's constraints $1,\dots,m$ are indexed by `Fin m` (index $i$ is the paper's $i+1$); constraint $i$ is an inequality exactly when $i < m_I$. Hence the paper's $\gamma_1$ is `γ 0`. Optimal values are infima in the extended reals `EReal`.
-- source:
--   arXiv:1911.09195v3, §4.3, proof of Proposition 2, p. 22

import Mathlib
import Definitions.Def_QCQPTightness_Sharp_QCQP
import Definitions.Def_QCQPTightness_Sharp_Faces
import Definitions.Def_QCQPTightness_Sharp_Mult
import Definitions.Def_QCQPTightness_Sharp_Examples

namespace QCQPTightness.Sharp

/-- §4.3, proof of Proposition 2, p. 22: for the QCQP (13), Assumption 3 holds and
`Γ = {γ : γ₁ ≥ 0, A(γ) ⪰ 0} = {γ : γ₁ ≥ 1}` (the paper's `γ₁` is `γ 0`). -/
theorem qcqp13_gamma (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (qcqp13 n k hn).Assumption3 ∧ (qcqp13 n k hn).Gamma = {γ | 1 ≤ γ 0} := by sorry

end QCQPTightness.Sharp
