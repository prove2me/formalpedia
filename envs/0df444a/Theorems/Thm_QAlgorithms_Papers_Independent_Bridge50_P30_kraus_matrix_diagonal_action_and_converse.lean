-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P30_kraus_matrix_diagonal_action_and_converse
-- name    : QAlgorithms.Papers.Independent.Bridge50.P30.kraus_matrix_diagonal_action_and_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:34:15.639776+00:00
-- url     : https://prove2.me/theorems/cb9fc2a2-b5ec-49db-a079-e0f3c280639c
-- title:
--   Kraus matrix action on diagonal states and converse stochastic lift
-- statement:
--   Fix $N\ge1$ and the coordinate orthonormal basis of $\mathbb C^N$. A probability vector has nonnegative real entries summing to one. A bi-stochastic real matrix has nonnegative entries and every row and column sum equal to one. For a bi-stochastic quantum operation $\Phi$ (complex-linear, completely positive, trace-preserving and identity-preserving), define its Kraus matrix by $B(\Phi)_{ij}=\sum_\mu |(M_\mu)_{ij}|^2$ for any Kraus family $(M_\mu)$ representing $\Phi$.
--
--   1. If $\rho$ is a positive semidefinite trace-one matrix diagonal in this basis, set $\sigma=\Phi(\rho)$, $p_j=\rho_{jj}$ and $q_j=\sigma_{jj}$. Then $p,q$ are probability vectors and
--
--   $$
--   q=B(\Phi)p.
--   $$
--
--   The entries of $p$ are the full eigenvalue list of $\rho$, with multiplicity; $\sigma$ need not be diagonal, and $q$ consists of its basis measurement probabilities.
--
--   2. Conversely, if $p,q$ are probability vectors and $T$ is bi-stochastic with $q=Tp$, then there is a bi-stochastic quantum operation $\Phi$ such that
--
--   $$
--   T=B(\Phi),\qquad\operatorname{diag}(q)=\Phi(\operatorname{diag}(p)).
--   $$
--
--   This links quantum channels to classical stochastic action and realizes every bi-stochastic matrix by a channel on the diagonal states.
-- source:
--   Von Neumann Entropy-Preserving Quantum Operations, arXiv:1104.2992v4, PDF p. 5, Lemma 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P30

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P30

open QAlgorithms.Papers.Independent.Information100.P50
  (M Lin choiMatrix hilbertSchmidtAdjoint)

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- PDF p.5, Lemma 3.1, both directions. The proof's basis diagonalizes rho;
the forward output need not be diagonal. In the converse the proof constructs
the two diagonal states from p and q. The printed T^T = [t_ij] means
Phi_T(|i><i|) = sum_j T_ji |j><j|, consistently with q = T p. -/
theorem kraus_matrix_diagonal_action_and_converse
    {N : ℕ} (hN : 0 < N) :
    (∀ (Phi : Lin N N) (rho : M N),
      IsBistochastic Phi → IsDensityMatrix rho →
      rho = Matrix.diagonal (fun j => rho j j) →
      let p : Fin N → ℝ := fun j => (rho j j).re
      let q : Fin N → ℝ := fun j => (Phi rho j j).re
      p ∈ stdSimplex ℝ (Fin N) ∧ q ∈ stdSimplex ℝ (Fin N) ∧
        q = (krausMatrix Phi).mulVec p) ∧
    (∀ (p q : Fin N → ℝ) (T : Matrix (Fin N) (Fin N) ℝ),
      p ∈ stdSimplex ℝ (Fin N) → q ∈ stdSimplex ℝ (Fin N) →
      T ∈ doublyStochastic ℝ (Fin N) → q = T.mulVec p →
      ∃ Phi : Lin N N, IsBistochastic Phi ∧ T = krausMatrix Phi ∧
        Matrix.diagonal (fun j => (q j : ℂ)) =
          Phi (Matrix.diagonal (fun j => (p j : ℂ)))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P30

end
