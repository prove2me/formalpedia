-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_corollary_2_10
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.corollary_2_10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:50:24.977416+00:00
-- url     : https://prove2.me/theorems/963fb374-2198-4718-954f-fb5792dc76f4
-- title:
--   Corollary 2.10
-- statement:
--   For every $n\geq0$, $GZ(n)$ is maximal among commutative subalgebras of $\mathbb C[S_n]$. For each irreducible class $\lambda$, construct the canonical subspace $V_T$ by intersecting the isotypic subspaces along an actual branching path $T$ ending at $\lambda$. For any chosen invariant positive definite Hermitian inner product there is a basis $(v_T)$ of unit vectors with
--
--   $$v_T\in V_T,\qquad V_T=\mathbb C v_T.$$
--
--   Thus the Gelfand–Tsetlin basis lines are determined up to scalar factors. The lines are constructed independently of this conclusion.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 13, Corollary 2.10

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Corollary 2.10 (PDF p.13). In addition to maximal commutativity,
each actual irreducible has a basis on its canonical path lines and each such
line consists exactly of scalar multiples of its basis vector. Unit length
uses the chosen invariant positive definite Hermitian inner product of p.7. -/
theorem corollary_2_10 (n : ℕ) :
    IsMaximalCommutative (gzAlgebra n) ∧
    (∀ C : IrreducibleClass n,
      ∀ H : InvariantHermitian (classRepresentative C).action,
      ∃ B : Module.Basis (BranchingPathsToClass C) ℂ (Fin (classRepresentative C).dimension → ℂ),
        ∀ T : BranchingPathsToClass C, B T ∈ canonicalLine C T.val ∧
          hermitianPair H.gram (B T) (B T) = 1 ∧
          ∀ v ∈ canonicalLine C T.val, ∃ c : ℂ, v = c • B T) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
