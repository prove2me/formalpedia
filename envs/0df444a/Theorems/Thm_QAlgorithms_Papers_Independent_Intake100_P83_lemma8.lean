-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_lemma8
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.lemma8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:23:56.401103+00:00
-- url     : https://prove2.me/theorems/514e1095-2fa6-45ce-9ec6-de8f2a47769e
-- title:
--   Lemma 8: basis paths characterize the actual commutant components
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   For $1\le k\le n$, form the joint-eigenspace blocks $\mathcal H_C$ of the actual commutant of $\mathcal V_{n,k}$. Their full physical spans are nonzero, orthogonal, complete, charge-refining, invariant and irreducible. For basis strings $r,s$, let $C$ be the component containing $r$. Then
--
--   $$
--   r,s\in C\quad\Longleftrightarrow\quad
--   \exists\ r=s_0,s_1,\ldots,s_m=s\text{ all in }C,
--   \quad d(s_j,s_{j+1})\le k.
--   $$
--
--   Here $d$ is Hamming distance, and $m=0$ is allowed. The component relation is defined from the actual commutant rather than from the paths, so identification with the actual invariant spaces is theorem content.
--
--   This relates the operator-theoretic components to finite redistributions in the product basis.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 12, Lemma 8: basis paths characterize invariant components

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF pp.12-13 Lemma 8: commutant-defined actual irreducible components are characterized
by the stated within-component paths. The identification with actual invariant subspaces
is included as conclusion, so this is not a tautology about graph components. -/
theorem lemma8 [CommGroup G] [Nonempty A] (chi : A → G → ℂ) (hchi : IsOnsite chi)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ComponentDecomposition chi n k ∧
    ∀ r s : Words A n, component chi n k r s ↔
      basisPath k (fun t => component chi n k r t) r s := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
