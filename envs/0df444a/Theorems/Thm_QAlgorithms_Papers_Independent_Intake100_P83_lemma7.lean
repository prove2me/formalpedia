-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_lemma7
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.lemma7
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:21:28.149891+00:00
-- url     : https://prove2.me/theorems/c085826d-19ca-4d9f-bf68-d918c0cbe5d8
-- title:
--   Lemma 7: diagonal unitaries with one exactly returned ancilla
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   Let $n\ge1$ and let $V$ be any unitary diagonal in the fixed product basis. Fix any normalized on-site state $a$ supported in a single on-site charge sector. There exists one $W\in\mathcal V_{n+1,2}$ such that, for every system vector $\psi$,
--
--   $$
--   W(\psi\otimes a)=(V\psi)\otimes a.
--   $$
--
--   The ancilla has the same on-site representation and is returned exactly; the implementing $W$ is independent of $\psi$. The equation for all vectors is the linear extension of the source's equation for all normalized states.
--
--   Thus diagonal phases can be synthesized even in the presence of extra invariant components.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 9, Lemma 7: diagonal unitaries with one returned ancilla

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF pp.9-10 Lemma 7: one same-representation ancilla in any fixed normalized charge
state implements every diagonal unitary and is returned exactly. The implementing W is
chosen before the universally quantified system vector. -/
theorem lemma7 [CommGroup G] [Nonempty A] (chi : A → G → ℂ) (hchi : IsOnsite chi)
    (n : ℕ) (hn : 1 ≤ n) (V : Op (Words A n))
    (hV : V ∈ Matrix.unitaryGroup (Words A n) ℂ) (hdiag : Matrix.IsDiag V)
    (a : EuclideanSpace ℂ A) (ha : QAlgorithms.IsState a) (hcharge : DefiniteCharge chi a) :
    ImplementsWithAncilla chi n 2 a V := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
