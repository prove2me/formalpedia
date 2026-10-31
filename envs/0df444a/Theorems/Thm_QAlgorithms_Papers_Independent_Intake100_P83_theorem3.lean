-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_theorem3
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.theorem3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:11:36.935106+00:00
-- url     : https://prove2.me/theorems/d6ebca7b-7174-4bb6-b124-47c3ce6a112d
-- title:
--   Theorem 3: independent special unitaries on the actual invariant components
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   Assume $2\le k\le n$. Construct components $C$ as the joint eigenspaces of the actual commutant: two basis strings are in the same component precisely when all commuting operators have the same diagonal entry on them. Let $\mathcal H_C$ be the full span of the strings in $C$. These spaces are nonzero, mutually orthogonal, complete, invariant and irreducible under $\mathcal V_{n,k}$, and each lies in one charge sector. Moreover,
--
--   $$
--   \bigoplus_C SU(\mathcal H_C)\subseteq\mathcal V_{n,k}
--   \subseteq\bigoplus_C U(\mathcal H_C),\qquad
--   [\mathcal V_{n,k},\mathcal V_{n,k}]=\bigoplus_C SU(\mathcal H_C).
--   $$
--
--   Thus different components admit independent determinant-one transformations, even when charge sectors split further.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 6, Theorem 3: independent full special-unitary groups on invariant components

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF p.6 Eqs.(9)-(11), proof pp.12-14, Theorem 3.
The blocks are constructed from the actual commutant, not supplied as hypotheses. -/
theorem theorem3 [CommGroup G] [Nonempty A] (chi : A → G → ℂ)
    (hchi : IsOnsite chi) (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    ComponentDecomposition chi n k ∧
    blockSpecial (component chi n k) ⊆ symmetricLocalGroup chi n k ∧
    symmetricLocalGroup chi n k ⊆ blockPreservingUnitaries (component chi n k) ∧
    derived (symmetricLocalGroup chi n k) = blockSpecial (component chi n k) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
