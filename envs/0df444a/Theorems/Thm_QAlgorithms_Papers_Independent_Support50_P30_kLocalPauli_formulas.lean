-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P30_kLocalPauli_formulas
-- name    : QAlgorithms.Papers.Independent.Support50.P30.kLocalPauli_formulas
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:27:19.239976+00:00
-- url     : https://prove2.me/theorems/2f68042b-ad4d-4205-8989-b3b5a2a5ae12
-- title:
--   Unnumbered generalization of Theorem 2 to k-local Pauli sums
-- statement:
--   Fix $0\le k\le n$, one Pauli matrix $\chi\in\{X,Y,Z\}$, and let $A_\chi^{(k)}$ be the sum of the corresponding Pauli string over each $k$-element subset of qubits exactly once. Put $K_k(w;n)=\sum_{l=0}^k\binom{n-w}{k-l}\binom wl(-1)^l$. In the computational basis for $\chi=Z$,
--
--   $$A_Z^{(k)}|z\rangle=K_k(w(z);n)|z\rangle.$$
--
--   For the common block in any fixed Schur sector $\lambda=(n-m,m)$, with $d_\lambda=n-2m+1$, all three choices of $\chi$ satisfy
--
--   $$\operatorname{Tr}A_{\chi,\lambda}^{(k)}=\sum_{w=m}^{n-m}K_k(w;n),\qquad
--   \operatorname{Tr}\bigl((A_{\chi,\lambda}^{(k)})^2\bigr)=\sum_{w=m}^{n-m}K_k(w;n)^2,$$
--   $$\Delta(A_{\chi,\lambda}^{(k)})=\sum_{w=m}^{n-m}K_k(w;n)^2-\frac{\bigl(\sum_{w=m}^{n-m}K_k(w;n)\bigr)^2}{d_\lambda}.$$
--
--   At $k=0$ the operator is the identity and its centered statistic is zero. The formulas extend the three special families of Theorem 2.
-- source:
--   Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks, arXiv:2210.09974v3, PDF p. 29, Unnumbered generalization of Theorem 2 to k-local Pauli sums

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF p.29, Eqs.(61)-(65): computational eigenvalue, trace, squared trace,
and Delta. The weight range m,...,n-m has exactly d_lambda entries. -/
theorem kLocalPauli_formulas {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (S : SchurFrame n) (m : Sector n)
    (chi : Matrix Bool Bool ℂ) (hchi : chi ∈ ({pauliX, pauliY, pauliZ} : Set _)) :
    (∀ z : Qubits n, act (collective n pauliZ k) (ket z) =
      (krawtchouk n k (hammingWeight z) : ℂ) • ket z) ∧
    (commonBlock S m (collective n chi k)).trace.re =
      ∑ j : Fin (blockDim n m), krawtchouk n k (m.val + j.val) ∧
    ((commonBlock S m (collective n chi k)) ^ 2).trace.re =
      ∑ j : Fin (blockDim n m), (krawtchouk n k (m.val + j.val)) ^ 2 ∧
    centeredDelta (commonBlock S m (collective n chi k)) =
      (∑ j : Fin (blockDim n m), (krawtchouk n k (m.val + j.val)) ^ 2) -
      (∑ j : Fin (blockDim n m), krawtchouk n k (m.val + j.val)) ^ 2 /
        (blockDim n m : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Support50.P30

end
