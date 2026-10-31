-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_central_prefix_spans
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.central_prefix_spans
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:40:58.803996+00:00
-- url     : https://prove2.me/theorems/bb4fc094-5dda-42dd-8e02-ed0f110bdfa8
-- title:
--   Corollary 2: equality of central prefix spans
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   For $0\le2\mu\le n$, define
--   $$C_\mu=\sum_{a+b+c=\mu}\frac{(2a)!(2b)!(2c)!}{a!b!c!}P_{2a,2b,2c}.$$
--   In particular $C_0=I$.
--
--   Let $T_\mu$ consist of permutations with exactly $\mu$ disjoint transpositions and all other points fixed, and let $L_\mu=\sum_{\pi\in T_\mu}R(\pi)$, where $R(\pi)|b\rangle=|b\circ\pi^{-1}\rangle$.
--   For $2\mu\le n$,
--   $$\operatorname{span}_{\mathbb R}\{L_0,\ldots,L_\mu\}=\operatorname{span}_{\mathbb R}\{C_0,\ldots,C_\mu\}.$$
--   In particular, the full families with $0\le j\le\lfloor n/2\rfloor$ have the same real span.
--
--   The families are prefixes, rather than a single $L_\mu$: this is the interpretation supplied by the triangular identity (B13).
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 12, corollary2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.12–13, Corollary 2: PREFIX spans, not a singleton L_mu span.
The triangular identity (B13) supplies the intended reading. -/
theorem central_prefix_spans {n mu : ℕ} (hmu : 2 * mu ≤ n) :
    Submodule.span ℝ {A | ∃ j : ℕ, j ≤ mu ∧ A = transpositionSum n j} =
      Submodule.span ℝ {A | ∃ j : ℕ, j ≤ mu ∧ A = centralElement n j} ∧
    Submodule.span ℝ {A | ∃ j : ℕ, 2 * j ≤ n ∧ A = transpositionSum n j} =
      Submodule.span ℝ {A | ∃ j : ℕ, 2 * j ≤ n ∧ A = centralElement n j} := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
