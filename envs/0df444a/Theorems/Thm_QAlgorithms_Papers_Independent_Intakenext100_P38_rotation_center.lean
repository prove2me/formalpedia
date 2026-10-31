-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_rotation_center
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.rotation_center
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:39:10.369993+00:00
-- url     : https://prove2.me/theorems/33dd71db-814d-4c2e-bd96-629bd7ded022
-- title:
--   Proposition 2: center of the collective-rotation commutant
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   For $0\le2\mu\le n$, define
--   $$C_\mu=\sum_{a+b+c=\mu}\frac{(2a)!(2b)!(2c)!}{a!b!c!}P_{2a,2b,2c}.$$
--   In particular $C_0=I$.
--   Let $\mathfrak v_n=\{A:A^\dagger=-A,\ [A,U^{\otimes n}]=0\text{ for every }U\in U(2)\}$. Then, for every $n\ge0$,
--   $$\mathfrak z(\mathfrak v_n)=\operatorname{span}_{\mathbb R}\{iC_\mu:0\le2\mu\le n\}.$$
--
--   This gives the center on the other side of Schur–Weyl duality, without assuming its equality to the permutation-equivariant center.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 11, proposition2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.11,13, Proposition 2: the collective-U(2) commutant is a different
algebra from the permutation commutant; its center is stated independently. -/
theorem rotation_center (n : ℕ) :
    algebraCenter (rotationCommutant n) =
      Submodule.span ℝ {A | ∃ mu : ℕ, 2 * mu ≤ n ∧
        A = Complex.I • centralElement n mu} := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
