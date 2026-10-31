-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_correction_dependency
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.correction_dependency
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:46:48.656205+00:00
-- url     : https://prove2.me/theorems/570770b1-fbf8-4b9b-acb6-b328badb0bfd
-- title:
--   Dependency of the constructed correction matrices
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   In Note G's convention put $\widetilde P_{xyz}=i(-1)^yP_{xyz}$, implementing both $Y\mapsto-Y$ and $P\mapsto iP$. Define
--   $$A=-4\widetilde P_{k-2,2,0}+2k\widetilde P_{k,0,0},\quad B=4\widetilde P_{k-2,0,2}-2k\widetilde P_{k,0,0},$$
--   $$C=-4(k-2)\widetilde P_{k-2,2,0}-4\widetilde P_{k-2,0,2}+2k(k-1)\widetilde P_{k,0,0}.$$
--
--   For $2\le k\le n$,
--   $$C=(k-2)A-B.$$
--   Consequently the family $(A,B,C)$ is not linearly independent over $\mathbb R$.
--
--   This is the explicit dependency responsible for the failed independence step in Ref. [32], with $A,B,C$ constructed from (G4)–(G6).
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 22, eq-G7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF p.22, (G4)–(G7): the constructed matrices satisfy the dependency.
The nonzero relation coefficient on C makes failure of linear independence explicit. -/
theorem correction_dependency {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    correctionC n k = ((k : ℝ) - 2) • correctionA n k - correctionB n k ∧
    ¬ LinearIndependent ℝ (![correctionA n k, correctionB n k, correctionC n k] :
      Fin 3 → QnnOperator n) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
