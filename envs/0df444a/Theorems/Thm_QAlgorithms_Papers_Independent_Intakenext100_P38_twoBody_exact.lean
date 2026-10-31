-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_twoBody_exact
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.twoBody_exact
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:30:36.214666+00:00
-- url     : https://prove2.me/theorems/87bae3df-f96d-4029-a7a2-55121fb8ca90
-- title:
--   Theorem 1: exact two-body algebra
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Write $\mathfrak u_n$ for the skew-Hermitian commutant of the qubit-permuting representation of $S_n$, $\mathfrak s_n$ for its total-trace-zero subalgebra, and $\mathfrak d_n=[\mathfrak u_n,\mathfrak u_n]$ for its derived algebra, equivalently the algebra with independently traceless multiplicity blocks.
--
--   Let $G_2=\{P_{100},P_{010},P_{002}\}$ and let $\mathfrak g_2=\operatorname{Lie}_{\mathbb R}\{iH:H\in G_2\}$ be its actual dynamical Lie algebra.
--
--   For $0\le2\mu\le n$, define
--   $$C_\mu=\sum_{a+b+c=\mu}\frac{(2a)!(2b)!(2c)!}{a!b!c!}P_{2a,2b,2c}.$$
--   In particular $C_0=I$.
--   For $n\ge2$,
--   $$\mathfrak g_2=\mathfrak d_n+\operatorname{span}_{\mathbb R}\{iC_1\},\qquad \dim\operatorname{span}_{\mathbb R}\{iC_1\}=1,$$
--   and this central line lies in $\mathfrak z(\mathfrak u_n)$. Consequently $\mathfrak g_2$ is semi-universal and subspace controllable. For $n\ge4$ it is not universal up to a global phase.
--
--   This identifies the exact relative-phase direction that remains accessible. The non-universality qualification corrects the unqualified abstract: at $n=2,3$ the central line is the only traceless central direction.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 4, Theorem 1 / abstract: exact two-body dynamical Lie algebra

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.4–6, Theorem 1, (24)–(25): exact algebra and generated central line.
Source correction: nonuniversality only for n>=4; n=2,3 have only one traceless
central direction and are universal. The abstract's 'no control' is replaced by
this precise central line. -/
theorem twoBody_exact {n : ℕ} (hn : 2 ≤ n) :
    (g2 n).toSubmodule = centerlessSymmetricAlgebra n ⊔ centralSpan n 1 ∧
    centralSpan n 1 ≤ algebraCenter (symmetricUnitaryAlgebra n) ∧
    Module.finrank ℝ (centralSpan n 1) = 1 ∧
    IsSemiUniversal (g2 n).toSubmodule ∧
    IsSubspaceControllable (g2 n).toSubmodule ∧
    (4 ≤ n → ¬ IsEquivariantlyUniversal (g2 n).toSubmodule) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
