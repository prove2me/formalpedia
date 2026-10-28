-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P43_alternative_nonnegative
-- name    : QAlgorithms.Papers.Independent.Support50.P43.alternative_nonnegative
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:30:38.382599+00:00
-- url     : https://prove2.me/theorems/6a73b3c7-fb3e-4438-85ce-c6f59e2519c0
-- title:
--   Alternative multipartite information is nonnegative
-- statement:
--   All entropies are von Neumann entropies in bits, with zero eigenvalues contributing zero. For a normalized positive semidefinite state $\rho$ on $n\ge2$ nonzero finite-dimensional local complex spaces, write $S(T)=S(\rho_T)$ for the marginal entropy, $[n]=\{1,\ldots,n\}$, and $\bar i=[n]\setminus\{i\}$. Define
--   $$
--   I(\rho)=\sum_{i=1}^n S(\bar i)-(n-1)S([n]),\qquad I_x(\rho)=\sum_{i=1}^n S(\{i\})-S([n]).
--   $$
--
--   For every such state,
--   $$I(\rho)\ge0.$$
--
--   This gives a nonnegative multipartite correlation functional without a normalization factor.
-- source:
--   Multiparty Quantum Mutual Information: An alternative definition, arXiv:1504.07176v2, PDF p. 3, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P43

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- These accepted register types are definitionally the required finite tensor bases.

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)

open QAlgorithms.Papers.Independent.Information100.P21 (ghzKet)

/-- Theorem 1, PDF pp.3–4: non-negativity, under the finite density-matrix convention. -/
theorem alternative_nonnegative {n : ℕ} (hn : 2 ≤ n) {D : Fin n → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho) :
    0 ≤ alternativeOn rho Finset.univ := by sorry

end QAlgorithms.Papers.Independent.Support50.P43

end
