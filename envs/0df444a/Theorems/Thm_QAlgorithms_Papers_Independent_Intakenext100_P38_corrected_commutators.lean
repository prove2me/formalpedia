-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_corrected_commutators
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.corrected_commutators
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:46:10.740313+00:00
-- url     : https://prove2.me/theorems/97c4e275-d077-4f4e-9299-c64c548c0b26
-- title:
--   Corrected commutation relations (G1)–(G3)
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   In Note G's convention put $\widetilde P_{xyz}=i(-1)^yP_{xyz}$, implementing both $Y\mapsto-Y$ and $P\mapsto iP$. Define
--   $$A=-4\widetilde P_{k-2,2,0}+2k\widetilde P_{k,0,0},\quad B=4\widetilde P_{k-2,0,2}-2k\widetilde P_{k,0,0},$$
--   $$C=-4(k-2)\widetilde P_{k-2,2,0}-4\widetilde P_{k-2,0,2}+2k(k-1)\widetilde P_{k,0,0}.$$
--
--   For $2\le k\le n$,
--   $$[\widetilde P_{k-1,1,0},\widetilde P_{001}]=A,\qquad[\widetilde P_{k-1,0,1},\widetilde P_{010}]=B.$$
--   If additionally $k\ge4$, then
--   $$[\widetilde P_{k-2,1,0},\widetilde P_{101}]=-4(n-k+2)\widetilde P_{k-4,2,0}+2(k-2)(n-k+2)\widetilde P_{k-2,0,0}+C.$$
--
--   These are the present authors' combinatorial corrections to Ref. [32]. The separate lower bound on the third relation keeps every index legitimate.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 21, corrected-commutators

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.21–22, (G1)–(G3): the authors' corrected commutators, with Note G's
signed skew convention. The third relation requires k>=4 for legitimate indices. -/
theorem corrected_commutators {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    (appendixPauli n (k - 1) 1 0 * appendixPauli n 0 0 1 -
      appendixPauli n 0 0 1 * appendixPauli n (k - 1) 1 0 = correctionA n k) ∧
    (appendixPauli n (k - 1) 0 1 * appendixPauli n 0 1 0 -
      appendixPauli n 0 1 0 * appendixPauli n (k - 1) 0 1 = correctionB n k) ∧
    (4 ≤ k →
      appendixPauli n (k - 2) 1 0 * appendixPauli n 1 0 1 -
        appendixPauli n 1 0 1 * appendixPauli n (k - 2) 1 0 =
      (-4 * ((n : ℝ) - k + 2)) • appendixPauli n (k - 4) 2 0 +
        (2 * ((k : ℝ) - 2) * ((n : ℝ) - k + 2)) • appendixPauli n (k - 2) 0 0 +
        correctionC n k) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
