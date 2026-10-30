-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P12_bcs_qutrit_entanglementWitness
-- name    : QAlgorithms.Papers.Independent.Extend50.P12.bcs_qutrit_entanglementWitness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:49:15.564016+00:00
-- url     : https://prove2.me/theorems/28b76f29-658f-4d0b-af0a-3daa6918845a
-- title:
--   §III.A: a qutrit entanglement witness, Eqs.(21)–(25)
-- statement:
--   On $(\mathbb C^3)^{\otimes3}$, let $V(ij)$ interchange sites $i,j$ and let $T_j$ be ordinary partial transpose on site $j$ in the fixed product basis. Define
--   $$
--   W=V(12)^{T_2}+V(13)+\frac14 I-\frac1{10}V(23)^{T_2}.
--   $$
--   Then $W$ is block-positive across $1|23$ and is not positive semidefinite. Equivalently,
--   $$
--   \operatorname{tr}[W(A\otimes C)]\in\mathbb R_{\ge0}
--   \quad\text{for every }A\in M_3(\mathbb C),\ C\in M_9(\mathbb C)\text{ with }A,C\ge0,
--   \qquad W\not\ge0.
--   $$
--   Here $C$ is an arbitrary operator on the two output sites together, and no trace-one condition is imposed on the test matrices. The partially transposed swaps are unnormalized Bell operators.
--
--   Thus $W$ is the specified entanglement witness on the bipartition $1|23$, with $\alpha=1/4$ and $\beta=-1/10$.
-- source:
--   Positive maps from the walled Brauer algebra, arXiv:2112.12738v3, PDF p. 4, §III.A, Eqs.(21)-(25)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P12

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P12

attribute [local instance] Classical.propDecidable

/-- The qutrit entanglement witness of PDF p.4, Eqs.(21)-(25): block-positive
on the full 1|23 cut and not positive semidefinite. Bell operators are
unnormalized; alpha=1/4 and beta=-1/10. -/
theorem bcs_qutrit_entanglementWitness :
    InputOutputBlockPositive (r := 1) (m := 2) bcsWitness ∧ ¬ bcsWitness.PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Extend50.P12

end
