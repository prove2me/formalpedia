-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P36_cb_factorization_infimum
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P36.cb_factorization_infimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:15:01.388085+00:00
-- url     : https://prove2.me/theorems/b1d36152-ff64-4929-ac5a-72f0d076141e
-- title:
--   Corollary 20: the infimum over all generalized representations
-- statement:
--   Let $n,k\ge1$ and let $\phi:M_n\to M_k$ be complex-linear. Let $\mathcal R_\phi$ consist of every finite pair of families $A_i\in M_{k,n}$, $B_i\in M_{n,k}$ representing $\phi(X)=\sum_iA_iXB_i$ for every matrix $X$. This collection is nonempty, and
--
--   $$\|\phi\|_{\rm cb}=\|\phi^\dagger\|_\diamond=\inf_{(A,B)\in\mathcal R_\phi}\sqrt{\left\|\sum_i A_iA_i^\dagger\right\|}\sqrt{\left\|\sum_i B_i^\dagger B_i\right\|}.$$
--
--   The infimum allows arbitrary finite lengths, including the empty zero-map representation. The dual is characterized by $\operatorname{Tr}(\phi(X)Y)=\operatorname{Tr}(X\phi^\dagger(Y))$. Matrix norms are Euclidean operator norms, and trace norm is unnormalized.
--
--   The result turns the stabilized norm into an optimization over actual finite factorizations. Attainment with at most $nk$ terms is retained separately in Theorem 19.
-- source:
--   Computing Stabilized Norms for Quantum Operations via the Theory of Completely Bounded Maps, arXiv:0711.3636v1, PDF p. 8, Corollary 20

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P36

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P36

local notation "Mat" => QAlgorithms.Papers.Independent.Information100.P50.M

local notation "Map" => QAlgorithms.Papers.Independent.Information100.P50.Lin

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

/-- Corollary 20, PDF p.8: all finite generalized representations, without a
length cap in the infimum; nonemptiness is asserted rather than assumed. -/
theorem cb_factorization_infimum {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (phi : Map n k) :
    (representationCosts phi).Nonempty ∧
    extendedCBNorm phi = rectangularDiamondNorm (traceDual phi) ∧
    extendedCBNorm phi = sInf (representationCosts phi) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P36

end
