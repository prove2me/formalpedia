-- Prove2me | Theorems.Thm_QCQPTightness_Sharp_qcqp13_affdim
-- name    : QCQPTightness.Sharp.qcqp13_affdim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:24:28.940993+00:00
-- url     : https://prove2.me/theorems/ace142ba-3c07-4731-9881-417fb864fcf7
-- title:
--   §4.3, proof of Proposition 2, p. 22 — aff dim({b(γ) : γ₁ = 1}) = k for (13)
-- statement:
--   For the QCQP (13) with positive $n$,
--   $$
--   \operatorname{aff\,dim}\big(\{b(\gamma) : \gamma_1=1\}\big)=k ,
--   $$
--   where $\gamma$ ranges over all of $\mathbb R^m$ with $\gamma_1=1$.
--
--   Together with the description of $\Gamma$ this shows that (13) meets the multiplicity bound $k\ge\operatorname{aff\,dim}\{b(\gamma):\gamma\in\mathcal F\}$ of Proposition 2 with equality, one short of the hypothesis of Theorems 1 and 2.
--
--   **Formalization Note** The paper's constraints $1,\dots,m$ are indexed by `Fin m` (index $i$ is the paper's $i+1$); constraint $i$ is an inequality exactly when $i < m_I$. Hence the paper's $\gamma_1$ is `γ 0`. Optimal values are infima in the extended reals `EReal`. The statement holds for every $k$, including $k=0$.
-- source:
--   arXiv:1911.09195v3, §4.3, proof of Proposition 2, p. 22

import Mathlib
import Definitions.Def_QCQPTightness_Sharp_QCQP
import Definitions.Def_QCQPTightness_Sharp_Faces
import Definitions.Def_QCQPTightness_Sharp_Mult
import Definitions.Def_QCQPTightness_Sharp_Examples

namespace QCQPTightness.Sharp

/-- §4.3, proof of Proposition 2, p. 22: for the QCQP (13), `aff dim({b(γ) : γ₁ = 1}) = k`. -/
theorem qcqp13_affdim (n k : ℕ) (hn : 0 < n) :
    affdim ((qcqp13 n k hn).bγ '' {γ | γ 0 = 1}) = k := by sorry

end QCQPTightness.Sharp
