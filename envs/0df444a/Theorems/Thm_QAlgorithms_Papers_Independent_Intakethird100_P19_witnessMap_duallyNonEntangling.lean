-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_witnessMap_duallyNonEntangling
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.witnessMap_duallyNonEntangling
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:38:41.821757+00:00
-- url     : https://prove2.me/theorems/617c9d04-e74a-4245-90e0-cac36b96c3d0
-- title:
--   Lemma 12: a channel from a bounded entanglement witness
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. Let $W$ be Hermitian and satisfy $\operatorname{Tr}(W\sigma)\ge0$ for every separable state, and let $\|W\|_F\le1$ be its Frobenius norm. Define $A=(W+2I)/3$ and
--
--   $$\Lambda(X)=\operatorname{Tr}(AX)\frac{I_4}{4}+\operatorname{Tr}((I-A)X)\phi_2^+.$$
--
--   Then $\Lambda$ is a channel and both $\Lambda$ and its trace dual preserve the separable positive cone.
--
--   This is the witness conversion construction used for distillability.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 16, Lemma 12

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P19

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P19

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P19 (Bip)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

/-- Lemma 12, PDF pp.16-17: every witness of Frobenius norm at most one
constructs the specified dually non-entangling channel of Eq.(21). -/
theorem witnessMap_duallyNonEntangling {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (W : Bip a b) (hw : Witness W) (hnorm : frobenius W ≤ 1) :
    IsChannel (witnessMap W) ∧ DNE (witnessMap W) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
