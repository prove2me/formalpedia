-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_stabilizerTensorInvariance
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.stabilizerTensorInvariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:09:15.315533+00:00
-- url     : https://prove2.me/theorems/d211f44e-baca-4347-b1dc-5c8cf7382869
-- title:
--   Stabilizer tensor symmetries
-- statement:
--   Let $d$ be prime, $t\geq1$, and let $|S\rangle$ be any normalized pure stabilizer on $n$ qudits. Every stochastic Lagrangian relation has expectation one on $|S\rangle^{\otimes t}$. Every unitary graph operator from $O_t(d)$ fixes that vector. The vector assertion is restricted to graph operators.
--
--   $$
--   \langle S^{\otimes t}|R(T)|S^{\otimes t}\rangle=1,\qquad R(O)|S\rangle^{\otimes t}=|S\rangle^{\otimes t}.
--   $$
--
--   This gives the source's stabilizer tensor symmetries in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 34, stabilizer-tensor-invariance

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF pp.34--35, (4.10),(4.13): expectation for every relation; vector invariance only for graphs. -/
theorem stabilizerTensorInvariance (d n t : ℕ) [NeZero d] [Fact (Nat.Prime d)]
    (ht : 1 ≤ t) (v : EuclideanSpace ℂ (ResidueRegister d n)) (hv : IsStabilizer v) :
    (∀ T : Lagrangian d t,
      inner ℂ (QAlgorithms.tensorPow t v) (QAlgorithms.act (tensorRelation n T.val) (QAlgorithms.tensorPow t v)) = 1) ∧
    (∀ O : StochasticOrthogonal d t,
      QAlgorithms.act (tensorRelation n (graphRelation O.val)) (QAlgorithms.tensorPow t v) = QAlgorithms.tensorPow t v) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
