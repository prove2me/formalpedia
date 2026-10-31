-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_theorem2prime
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.theorem2prime
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:09:40.415251+00:00
-- url     : https://prove2.me/theorems/33eccab0-00ea-4d8a-aab9-91b8b2fa34e2
-- title:
--   Theorem 2′: semi-universality, commutants and basis transitivity
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   Assume $2\le k\le n$. Let $q_n$ be the number of occurring charges and $\mathcal C_{n,k}$ the complex operator commutant of $\mathcal V_{n,k}$. The following conditions are equivalent:
--
--   $$
--   \bigoplus_\mu SU(\mathcal H_\mu)\subseteq\mathcal V_{n,k},\qquad
--   \mathcal C_{n,k}=\mathcal C_{n,n}=\operatorname{span}_{\mathbb C}\{U_n(g):g\in G\},\qquad
--   \dim_{\mathbb C}\mathcal C_{n,k}=q_n,
--   $$
--
--   and the condition that any two equal-charge basis strings can be joined by a finite path of equal-charge strings with consecutive Hamming distances at most $k$. The path contains both endpoints and can have one vertex.
--
--   This identifies the exact obstruction to semi-universality with extra conserved observables and with failure of classical charge redistribution.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 7, Introduction pp.1–2; Theorem 2prime (printed Theorem 2′), IV A

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF pp.6-7,15, Theorem 2 prime: all three conditions, including the dimension formulation.
The path includes endpoints and may consist of one vertex. -/
theorem theorem2prime [CommGroup G] [Nonempty A] (chi : A → G → ℂ)
    (hchi : IsOnsite chi) (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    (SemiUniversal chi n k ↔ NoExtra chi n k) ∧
    (NoExtra chi n k ↔ CommDimension chi n k) ∧
    (NoExtra chi n k ↔ TransitiveCharges chi n k) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
