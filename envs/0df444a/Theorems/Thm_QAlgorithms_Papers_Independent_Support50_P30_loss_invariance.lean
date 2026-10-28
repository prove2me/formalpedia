-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P30_loss_invariance
-- name    : QAlgorithms.Papers.Independent.Support50.P30.loss_invariance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:20:25.418984+00:00
-- url     : https://prove2.me/theorems/58f1dbc9-e1d8-4af8-880b-204c681dcf12
-- title:
--   Lemma 1 (Invariance from equivariance)
-- statement:
--   Let $G$ be a compact topological group with a continuous unitary representation $R$ on the $n$-qubit space. Let $U(\theta)=e^{-i\theta_LH_L}\cdots e^{-i\theta_1H_1}$, where every $H_j$ is Hermitian and commutes with every $R(g)$. Suppose that the Hermitian observable $O$ also commutes with every $R(g)$. For every parameter vector, density matrix $\rho$, and $g\in G$,
--
--   $$\operatorname{Tr}\!\left(U(\theta)R(g)\rho R(g)^\dagger U(\theta)^\dagger O\right)=\operatorname{Tr}\!\left(U(\theta)\rho U(\theta)^\dagger O\right).$$
--
--   Thus composing the equivariant circuit with the equivariant measurement gives an invariant loss. No assumption about learning labels is required.
-- source:
--   Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks, arXiv:2210.09974v3, PDF p. 3, Lemma 1 (Invariance from equivariance)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

/-- PDF p.3, Lemma 1; proof on p.22. -/
theorem loss_invariance {n L : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G]
    (R : G →* Matrix.unitaryGroup (Qubits n) ℂ) (hR : Continuous R)
    (H : Fin L → QnnOperator n) (hH : ∀ j, (H j).IsHermitian)
    (hcomm : ∀ j g, H j * (R g).val = (R g).val * H j)
    (O : QnnOperator n) (hO : O.IsHermitian)
    (hOcomm : ∀ g, O * (R g).val = (R g).val * O) :
    ∀ (theta : Fin L → ℝ) (rho : QnnDensity n) (g : G),
      qnnLoss (circuit H theta) ((R g).val * rho.val * (R g).val.conjTranspose) O =
        qnnLoss (circuit H theta) rho.val O := by sorry

end QAlgorithms.Papers.Independent.Support50.P30

end
