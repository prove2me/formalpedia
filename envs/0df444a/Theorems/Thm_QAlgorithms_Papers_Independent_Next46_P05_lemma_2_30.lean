-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_lemma_2_30
-- name    : QAlgorithms.Papers.Independent.Next46.P05.lemma_2_30
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:48:52.917349+00:00
-- url     : https://prove2.me/theorems/55834f87-f8a3-491c-ae68-6fe6b57e0419
-- title:
--   Lemma 2.30: vanishing Peirce coefficients of a square
-- statement:
--   Let $V$ be a finite-dimensional real unital euclidean Jordan algebra, with bilinear Jordan product, unit $e$, and a positive definite associative scalar product. Let $(c_1,\ldots,c_r)$ be a Jordan frame of nonzero primitive orthogonal idempotents summing to $e$. Let $y$ be a square, with Peirce decomposition $y=\sum_i\lambda_i c_i+\sum_{i<j}y_{ij}$, where $y_{ij}\in V_{1/2}(c_i)\cap V_{1/2}(c_j)$. For each index $i$ with $\lambda_i=0$,
--
--   $$y_{\ell i}=0\quad(\ell<i),\qquad y_{ij}=0\quad(j>i).$$
--
--   The two index ranges are independent, so the applicable half remains at $i=1$ or $i=r$. Simplicity of $V$ is not assumed. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 14, Lemma 2.30

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P05

namespace QAlgorithms.Papers.Independent.Next46.P05

noncomputable section

open Set

open QAlgorithms.Papers.Independent.Frontier30.P26
  (bracketSpan innerWord Invariant ClosedCone GeneratingInvariantCone CompactlyEmbedded)

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P05.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P05.lieNormedSpace

section JordanStatements

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- Lemma 2.30, PDF p. 14. Both halves survive at the endpoint indices. -/
theorem lemma_2_30 (J : EuclideanJordan V) {r : ℕ} (c : Fin r → V)
    (hf : JordanFrame J c) (y : V) (hy : y ∈ squares J)
    (lam : Fin r → ℝ) (off : Fin r → Fin r → V)
    (hp : ∀ i j, i < j → off i j ∈ peirce J (c i) (1 / 2) ⊓ peirce J (c j) (1 / 2))
    (hd : y = (∑ i, lam i • c i) + ∑ i, ∑ j, if i < j then off i j else 0)
    (i : Fin r) (hz : lam i = 0) :
    (∀ l : Fin r, l < i → off l i = 0) ∧ (∀ j : Fin r, i < j → off i j = 0) := by sorry

end JordanStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
