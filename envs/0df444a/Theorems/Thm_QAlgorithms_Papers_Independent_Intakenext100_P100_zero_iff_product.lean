-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P100_zero_iff_product
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P100.zero_iff_product
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:23:54.19706+00:00
-- url     : https://prove2.me/theorems/c5534977-47df-4208-8778-565a3be24023
-- title:
--   Zero measured correlation characterizes product states
-- statement:
--   Let $A$ and $B$ be arbitrary nonempty finite computational bases and let $\rho$ be a bipartite positive semidefinite matrix of trace one. Write $\rho_A=\operatorname{Tr}_B\rho$ and $\rho_B=\operatorname{Tr}_A\rho$. Then
--   $$I_c(\rho)=0\quad\Longleftrightarrow\quad\rho=\rho_A\otimes\rho_B.$$
--   Here $I_c$ is the optimum Shannon mutual information in bits over all independent finite local POVMs. This characterizes uncorrelated states without requiring equal local dimensions.
-- source:
--   Locking classical correlation in quantum states, arXiv:quant-ph/0303088v1, PDF p. 6, Corollary following Lemma 1; already stated on PDF p. 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P100

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P100

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.1 and p.4 footnote [12], explained p.6: zero classical correlation
characterizes the product of the actual marginals, in arbitrary positive
finite local dimensions, including singleton systems. -/
theorem zero_iff_product {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    lockingMeasuredInformation rho = 0 ↔
      rho = Matrix.kronecker (traceRight rho) (traceLeft rho) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P100

end
