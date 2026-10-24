-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P43_alternative_bounds
-- name    : QAlgorithms.Papers.Independent.Support50.P43.alternative_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:32:17.678983+00:00
-- url     : https://prove2.me/theorems/61818eed-a622-49e5-a9b7-8f398484aedb
-- title:
--   Lower and upper bounds in terms of CQMI
-- statement:
--   All entropies are von Neumann entropies in bits, with zero eigenvalues contributing zero. For a normalized positive semidefinite state $\rho$ on $n\ge2$ nonzero finite-dimensional local complex spaces, write $S(T)=S(\rho_T)$ for the marginal entropy, $[n]=\{1,\ldots,n\}$, and $\bar i=[n]\setminus\{i\}$. Define
--   $$
--   I(\rho)=\sum_{i=1}^n S(\bar i)-(n-1)S([n]),\qquad I_x(\rho)=\sum_{i=1}^n S(\{i\})-S([n]).
--   $$
--
--   For every such state, both inequalities hold:
--   $$I_x(\rho)-(n-2)S([n])\le I(\rho)\le I_x(\rho)+2S([n]).$$
--
--   These compare the two functionals while retaining the explicit dependence on the joint entropy and the number of parties.
-- source:
--   Multiparty Quantum Mutual Information: An alternative definition, arXiv:1504.07176v2, PDF p. 4, Theorem 4

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P43

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- These accepted register types are definitionally the required finite tensor bases.

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)

open QAlgorithms.Papers.Independent.Information100.P21 (ghzKet)

/-- Theorem 4, PDF p.4: both bounds, including the n-dependent lower bound. -/
theorem alternative_bounds {n : ℕ} (hn : 2 ≤ n) {D : Fin n → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho) :
    conventionalOn rho Finset.univ - (n - 2 : ℕ) * marginalEntropyBits rho Finset.univ ≤
      alternativeOn rho Finset.univ ∧
    alternativeOn rho Finset.univ ≤
      conventionalOn rho Finset.univ + 2 * marginalEntropyBits rho Finset.univ := by sorry

end QAlgorithms.Papers.Independent.Support50.P43

end
