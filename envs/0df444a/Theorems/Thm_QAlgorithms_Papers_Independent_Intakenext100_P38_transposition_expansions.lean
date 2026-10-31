-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_transposition_expansions
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.transposition_expansions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:40:29.181997+00:00
-- url     : https://prove2.me/theorems/1cc06aed-c3b7-4727-b66e-f7b261651d63
-- title:
--   Lemma 3: transposition-class expansions
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   For $0\le2\mu\le n$, define
--   $$C_\mu=\sum_{a+b+c=\mu}\frac{(2a)!(2b)!(2c)!}{a!b!c!}P_{2a,2b,2c}.$$
--   In particular $C_0=I$.
--
--   Let $T_\mu$ consist of permutations with exactly $\mu$ disjoint transpositions and all other points fixed, and let $L_\mu=\sum_{\pi\in T_\mu}R(\pi)$, where $R(\pi)|b\rangle=|b\circ\pi^{-1}\rangle$.
--   For each natural $\mu$ with $2\mu\le n$, both identities hold:
--   $$L_\mu=\frac{4^{-\mu}}{(n-2\mu)!}\sum_{a+b+c+f=\mu}\frac{(2a)!(2b)!(2c)!(n-2(\mu-f))!}{a!b!c!f!}P_{2a,2b,2c},$$
--   $$L_\mu=\frac{4^{-\mu}}{(n-2\mu)!}\sum_{j=0}^{\mu}\frac{(n-2j)!}{(\mu-j)!}C_j.$$
--   All indices are nonnegative and all factorial denominators are positive.
--
--   These identities relate the class-sum and Pauli central bases. The unbound $k$ in the printed first denominator is corrected to $\mu$ using (B17)–(B22).
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 12, lemma3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.12–13, Lemma 3: BOTH factorial formulas. Printed (B12) has an
unbound k in (n-2k)!; corrected to mu by (B17)–(B22). Ref.[18] overlap at p.13. -/
theorem transposition_expansions {n mu : ℕ} (hmu : 2 * mu ≤ n) :
    transpositionSum n mu = transpositionPauliExpansion n mu ∧
    transpositionSum n mu = transpositionCentralExpansion n mu := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
