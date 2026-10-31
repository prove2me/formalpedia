-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_theorem2
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.theorem2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:10:49.42899+00:00
-- url     : https://prove2.me/theorems/990e835b-27e2-4a16-94e9-edf6d5ef5552
-- title:
--   Theorem 2: equality of commutants iff semi-universality
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   For $2\le k\le n$, let $q_n$ count the occurring characters. Then
--
--   $$
--   \operatorname{Comm}(\mathcal V_{n,k})=\operatorname{Comm}(\mathcal V_{n,n})
--   =\operatorname{span}_{\mathbb C}\{U_n(g):g\in G\}
--   \quad\Longleftrightarrow\quad
--   \bigoplus_\mu SU(\mathcal H_\mu)\subseteq\mathcal V_{n,k}.
--   $$
--
--   Equivalently, the commutant on the left has complex dimension $q_n$ if and only if the inclusion on the right holds. This is the separately numbered commutant criterion for semi-universality.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 6, Theorem 2: equality of commutants iff semi-universality

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF pp.6,15, Theorem 2: equality of the actual complex commutants iff semi-universality. -/
theorem theorem2 [CommGroup G] [Nonempty A] (chi : A → G → ℂ)
    (hchi : IsOnsite chi) (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    (NoExtra chi n k ↔ SemiUniversal chi n k) ∧
    (CommDimension chi n k ↔ SemiUniversal chi n k) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
