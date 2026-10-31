-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_ancillaBlockUniversality
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.ancillaBlockUniversality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:22:02.71758+00:00
-- url     : https://prove2.me/theorems/376a15c3-bfef-4ce1-a840-1019ae79577b
-- title:
--   One ancilla elevates the original component SU blocks to U blocks
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   Assume $2\le k\le n$ and fix a normalized ancilla state $a$ of definite on-site charge. Let $\mathcal H_C$ be the actual irreducible components determined by the commutant of the system group $\mathcal V_{n,k}$. Every $V\in\bigoplus_CU(\mathcal H_C)$ has an implementation $W\in\mathcal V_{n+1,k}$ with
--
--   $$
--   \forall\psi,\qquad W(\psi\otimes a)=(V\psi)\otimes a.
--   $$
--
--   If the system has no extra conserved observables, the same conclusion holds for every $V\in\mathcal V_{n,n}$. Each implementing $W$ is chosen before the system input.
--
--   This supplies every indicated original block unitary using one returned ancilla; it does not assert that every extra component constraint disappears.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 10, VI, unnumbered: elevate component special unitaries using one ancilla

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF pp.4,10: one returned charge-state ancilla gives all independent U blocks of the
original component decomposition. Under no extra conserved observables it gives all
symmetric system unitaries. No claim that arbitrary type-II constraints disappear is made. -/
theorem ancillaBlockUniversality [CommGroup G] [Nonempty A] (chi : A → G → ℂ)
    (hchi : IsOnsite chi) (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (a : EuclideanSpace ℂ A) (ha : QAlgorithms.IsState a) (hcharge : DefiniteCharge chi a) :
    (∀ V ∈ blockPreservingUnitaries (component chi n k), ImplementsWithAncilla chi n k a V) ∧
    (NoExtra chi n k → ∀ V ∈ symmetricLocalGroup chi n n, ImplementsWithAncilla chi n k a V) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
