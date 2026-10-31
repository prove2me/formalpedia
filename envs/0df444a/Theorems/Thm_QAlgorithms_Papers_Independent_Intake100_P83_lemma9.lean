-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_lemma9
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.lemma9
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:24:37.868436+00:00
-- url     : https://prove2.me/theorems/0a888129-d514-4809-b3f5-1edec0490837
-- title:
--   Lemma 9: exact localized two-level X, Y and Z evolutions
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   Assume $2\le k\le n$. Let $r\ne s$ have equal charge and Hamming distance at most $k$. Define operators on the full system, zero outside the indicated two-level space, by
--
--   $$
--   X=|r\rangle\langle s|+|s\rangle\langle r|,\qquad
--   Y=i(|r\rangle\langle s|-|s\rangle\langle r|),\qquad
--   Z=|r\rangle\langle r|-|s\rangle\langle s|.
--   $$
--
--   Then for every $0\le\theta<2\pi$,
--
--   $$
--   e^{i\theta X},\ e^{i\theta Y},\ e^{i\theta Z}\in\mathcal V_{n,k}.
--   $$
--
--   The sign of $Y$ is the paper's sign, and $Z=(i/2)[X,Y]$. This isolates two-level evolutions without disturbing the other basis vectors.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 13, Lemma 9: localized two-level X,Y,Z evolution

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF pp.13-14 Lemma 9 and Eq.(33): all three localized two-level evolutions, with
Y = +i(|r><s|-|s><r|), are exactly synthesizable for k >= 2. -/
theorem lemma9 [CommGroup G] [Nonempty A] (chi : A → G → ℂ) (hchi : IsOnsite chi)
    (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (r s : Words A n)
    (hrs : r ≠ s) (hcharge : sameCharge chi n r s) (hdistance : hammingDist r s ≤ k) :
    ∀ theta ∈ Set.Ico (0 : ℝ) (2 * Real.pi),
      positiveImaginaryEvolution (twoX r s) theta ∈ symmetricLocalGroup chi n k ∧
      positiveImaginaryEvolution (twoY r s) theta ∈ symmetricLocalGroup chi n k ∧
      positiveImaginaryEvolution (twoZ r s) theta ∈ symmetricLocalGroup chi n k := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
