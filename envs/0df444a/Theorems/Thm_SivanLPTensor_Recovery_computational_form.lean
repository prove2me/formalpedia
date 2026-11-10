-- Prove2me | Theorems.Thm_SivanLPTensor_Recovery_computational_form
-- name    : SivanLPTensor.Recovery.computational_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T05:35:06.052813+00:00
-- url     : https://prove2.me/theorems/09b5bee3-7962-479f-86fb-b0a00d15b58d
-- title:
--   Corollary 3.2 (corrected: polynomial count in N and m)
-- statement:
--   Let $m=d+2\ge3$, let every mode dimension be positive, and let $T$ be any dense real tensor. Embed the standard basis column selected by a multi-index $\alpha$ in each direct-sum block, forming $E_\alpha$. For any covector frame $P$,
--   $$\Omega_P(T)=\sum_\alpha T[\alpha]\sum_{j<k}(-1)^{j+k+1}\det(PE_\alpha[\widehat{j,k}])\operatorname{Alt}(E_\alpha[j,k]).$$
--   The number of indexed summands is exactly $N\binom m2$. One finite scalar program computes this matrix from $T,P$ alone, uses no roots, and executes at most $CNm^5$ arithmetic operations, for one absolute positive constant $C$. This cost order comes from the complexity proof on printed page 9, rather than a numerical constant in the corollary.
--   This is the decomposition-free implementation interface. In unrestricted original dimensions the count is polynomial in $N,m$; it becomes polynomial in $N$ after the stated singleton preprocessing.
--
--   Differences from the source:
--   - correction: the unprocessed count N binomial(m,2) is poly(N) → the exact count is retained, with an executed O(N m^5) arithmetic bound, polynomial in N and m; reason: for every m≥3 take all n_j=1, r=1 and all factors 1: LP is vacuous and N=1 while binomial(m,2) is unbounded; after singleton preprocessing the main theorem still has poly(N) cost
--   - encoding: finite real modes and one-based indices → dependent Fin coordinates with zero-based indices; reason: the same finite arrays; parity in the signed minor formula is unchanged
--   - encoding: the determinant implementation and O(N m^5) arithmetic estimate in the complexity proof → one finite root-free scalar program and one absolute positive constant bounding its executed arithmetic count by C N m^5; reason: the execution predicate expands this contraction estimate directly; no root-cost function is quantified in this item
-- source:
--   Shiri Sivan, STOC 2027 submission #1294 (October 2026), Corollary 3.2, printed p. 6 / PDF p. 8, (5); complexity proof, printed p. 9 / PDF p. 11

import Definitions.Def_SivanLPTensor_Recovery_computationModel

namespace SivanLPTensor.Recovery
open scoped BigOperators

theorem computational_form :
    (∀ (d : ℕ) (n : Fin (d + 2) → ℕ), 1 ≤ d → (∀ j, 0 < n j) →
      ∀ (T : Tensor n) (P : Matrix (Fin d) (BlockIndex n) ℝ),
        omega T P = omegaFormula T P ∧
        Fintype.card ((j : Fin (d + 2)) → Fin (n j)) *
          (Finset.univ.filter (fun jk : Fin (d + 2) × Fin (d + 2) => jk.1 < jk.2)).card =
          inputSize n * Nat.choose (d + 2) 2) ∧
    ∃ p : Program, ∃ C : ℕ, ComputesContractions p C := by sorry

end SivanLPTensor.Recovery
