-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_rankOneDualBridge
-- name    : QAlgorithms.Papers.Independent.Information100.P21.rankOneDualBridge
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:49:46.904573+00:00
-- url     : https://prove2.me/theorems/203b7737-1498-4b73-97e0-aa4149f95595
-- title:
--   II.6 — Proposition II.6. If a standard-dual feasible triple (W, P, Q) has rank W = 1, then W is feasible for the generalized
-- statement:
--   Let $(W,P,Q)$ be standard-dual feasible on two qubits: all three operators are positive semidefinite and $I-W=P+Q^\Gamma$. If $\operatorname{rank}W=1$, then
--   $$W\succeq0,\qquad I-W^\Gamma\succeq0.$$
--   Thus $W$ is generalized-dual feasible. No input state or optimality assumption is needed.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 8, II.6 — Proposition II.6. If a standard-dual feasible triple (W, P, Q) has rank W = 1, then W is feasible for the generalized

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 8, Proposition II.6. If a standard-dual feasible triple (W, P, Q) has rank W = 1, then W is feasible for the generalized. -/
theorem rankOneDualBridge (W P Q : Op QQ) (hf : dualS W P Q) (hr : Matrix.rank W=1) : dualG W := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
