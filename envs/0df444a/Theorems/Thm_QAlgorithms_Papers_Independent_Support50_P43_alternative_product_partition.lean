-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P43_alternative_product_partition
-- name    : QAlgorithms.Papers.Independent.Support50.P43.alternative_product_partition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:33:09.785166+00:00
-- url     : https://prove2.me/theorems/c1c1010f-ed99-4459-bdaf-8bf9554bdad2
-- title:
--   Additivity across arbitrary product partitions
-- statement:
--   All entropies are von Neumann entropies in bits, with zero eigenvalues contributing zero. For a normalized positive semidefinite state $\rho$ on $n\ge2$ nonzero finite-dimensional local complex spaces, write $S(T)=S(\rho_T)$ for the marginal entropy, $[n]=\{1,\ldots,n\}$, and $\bar i=[n]\setminus\{i\}$. Define
--   $$
--   I(\rho)=\sum_{i=1}^n S(\bar i)-(n-1)S([n]),\qquad I_x(\rho)=\sum_{i=1}^n S(\{i\})-S([n]).
--   $$
--
--   Let $B_1,\ldots,B_m$ be any partition of $[n]$ into nonempty disjoint blocks, with $m\ge1$, and suppose $\rho=\bigotimes_{j=1}^m\rho_{B_j}$ after regrouping the registers. For a nonempty block $B$, put $I_B(\rho)=\sum_{i\in B}S(B\setminus\{i\})-(|B|-1)S(B)$, using $S(\varnothing)=0$. Then
--   $$I(\rho)=\sum_{j=1}^m I_{B_j}(\rho).$$
--
--   This includes singleton blocks, whose information is zero, and products across any partition of the physical parties.
-- source:
--   Multiparty Quantum Mutual Information: An alternative definition, arXiv:1504.07176v2, PDF p. 4, Theorem 5 and equation (15)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P43

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- These accepted register types are definitionally the required finite tensor bases.

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)

open QAlgorithms.Papers.Independent.Information100.P21 (ghzKet)

/-- Theorem 5 and (15), PDF p.4: additivity across ANY partition of the parties
on which the density matrix factors, allowing singleton blocks. -/
theorem alternative_product_partition {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m)
    {D : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho)
    (blocks : Fin m → Finset (Fin n))
    (hne : ∀ j, (blocks j).Nonempty)
    (hdis : ∀ j k, j ≠ k → Disjoint (blocks j) (blocks k))
    (hcover : Finset.univ.biUnion blocks = Finset.univ)
    (hprod : IsProductAcross rho blocks) :
    alternativeOn rho Finset.univ = ∑ j, alternativeOn rho (blocks j) := by sorry

end QAlgorithms.Papers.Independent.Support50.P43

end
