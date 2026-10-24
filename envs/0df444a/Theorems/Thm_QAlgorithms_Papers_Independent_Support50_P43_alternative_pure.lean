-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P43_alternative_pure
-- name    : QAlgorithms.Papers.Independent.Support50.P43.alternative_pure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:31:26.715147+00:00
-- url     : https://prove2.me/theorems/5013a1b9-a444-43d2-ad1d-3b28fa2abb6d
-- title:
--   Alternative information equals CQMI for pure states
-- statement:
--   All entropies are von Neumann entropies in bits, with zero eigenvalues contributing zero. For a normalized positive semidefinite state $\rho$ on $n\ge2$ nonzero finite-dimensional local complex spaces, write $S(T)=S(\rho_T)$ for the marginal entropy, $[n]=\{1,\ldots,n\}$, and $\bar i=[n]\setminus\{i\}$. Define
--   $$
--   I(\rho)=\sum_{i=1}^n S(\bar i)-(n-1)S([n]),\qquad I_x(\rho)=\sum_{i=1}^n S(\{i\})-S([n]).
--   $$
--
--   Let $\psi$ be any unit vector on the joint space and let $\rho=|\psi\rangle\langle\psi|$. Then
--   $$I(\rho)=I_x(\rho).$$
--
--   The two correlation functionals therefore agree throughout the pure-state regime.
-- source:
--   Multiparty Quantum Mutual Information: An alternative definition, arXiv:1504.07176v2, PDF p. 4, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P43

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- These accepted register types are definitionally the required finite tensor bases.

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)

open QAlgorithms.Papers.Independent.Information100.P21 (ghzKet)

/-- Theorem 2, PDF p.4: equality with CQMI for normalized pure states.
Neither zero joint entropy nor complementary-entropy equality is assumed. -/
theorem alternative_pure {n : ℕ} (hn : 2 ≤ n) {D : Fin n → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (psi : EuclideanSpace ℂ (RegisterBasis D)) (hpsi : ‖psi‖ = 1) :
    alternativeOn (pureDensity psi) Finset.univ =
      conventionalOn (pureDensity psi) Finset.univ := by sorry

end QAlgorithms.Papers.Independent.Support50.P43

end
