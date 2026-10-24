-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P30_efficientOverparametrization
-- name    : QAlgorithms.Papers.Independent.Support50.P30.efficientOverparametrization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:22:36.452752+00:00
-- url     : https://prove2.me/theorems/7926936a-a913-40bd-ac2c-dc8bbe668b79
-- title:
--   Theorem 3 (Efficient overparametrization)
-- statement:
--   There are constants $C>0$ and $N$ such that, for every $n\ge\max(N,2)$ and every normalized pure $n$-qubit input $\psi$, one can choose a generator word from Eq. (9), a parameter count $L$, and a parameter vector $\theta$ such that
--
--   $$L\le Cn^3,\qquad \operatorname{rank}F_{\psi}(\theta)\ge \operatorname{rank}F_{\psi}(t)$$
--
--   for every parameter vector $t$ of every finite generator word from the same gate-generator set. Here the QFIM of a circuit output $\psi(\theta)=U(\theta)\psi$ is $F_{jk}=4\operatorname{Re}(\langle\partial_j\psi|\partial_k\psi\rangle-\langle\partial_j\psi|\psi\rangle\langle\psi|\partial_k\psi\rangle)$. Thus an appropriate architecture with $O(n^3)$ parameters attains the maximum accessible QFIM rank. This is an existential saturation statement, not an optimizer-convergence assertion.
-- source:
--   Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks, arXiv:2210.09974v3, PDF p. 7, Theorem 3 (Efficient overparametrization)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

/-- PDF p.7, Theorem 3, using the saturation definition on pp.9,14-15.
The initial unit state precedes the existential schedule and parameters. -/
theorem efficientOverparametrization :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, 2 ≤ n →
    ∀ psi : EuclideanSpace ℂ (Qubits n), IsState psi →
    ∃ L : ℕ, (L : ℝ) ≤ C * (n : ℝ) ^ 3 ∧
    ∃ word : Fin L → Fin 3, ∃ theta : Fin L → ℝ,
    ∀ (Lother : ℕ) (other : Fin Lother → Fin 3) (t : Fin Lother → ℝ),
      (qfi (fun j => qnnGenerator n (other j)) t psi).rank ≤
        (qfi (fun j => qnnGenerator n (word j)) theta psi).rank := by sorry

end QAlgorithms.Papers.Independent.Support50.P30

end
