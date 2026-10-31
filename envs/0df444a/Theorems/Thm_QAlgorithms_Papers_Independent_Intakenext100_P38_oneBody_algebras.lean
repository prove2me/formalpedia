-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_oneBody_algebras
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.oneBody_algebras
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:31:12.248454+00:00
-- url     : https://prove2.me/theorems/6757cc5e-789c-4a57-8423-ec528e0dcc56
-- title:
--   One-body dynamical algebras
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Write $\mathfrak u_n$ for the skew-Hermitian commutant of the qubit-permuting representation of $S_n$, $\mathfrak s_n$ for its total-trace-zero subalgebra, and $\mathfrak d_n=[\mathfrak u_n,\mathfrak u_n]$ for its derived algebra, equivalently the algebra with independently traceless multiplicity blocks.
--   For $n\ge1$, let $\mathfrak g_1=\operatorname{Lie}_{\mathbb R}\{iP_{100}\}$ and $\mathfrak g'_1=\operatorname{Lie}_{\mathbb R}\{iP_{100},iP_{010}\}$. Then
--   $$\mathfrak g_1=\operatorname{span}_{\mathbb R}\{iP_{100}\},\quad\dim\mathfrak g_1=1,$$
--   $$\mathfrak g'_1=\operatorname{span}_{\mathbb R}\{iP_{100},iP_{010},iP_{001}\},\quad\dim\mathfrak g'_1=3.$$
--   These are respectively the collective representations of $\mathfrak u(1)$ and $\mathfrak{su}(2)$. For $n=1$ the latter is universal; for $n\ge2$ neither is subspace controllable.
--
--   The examples isolate the expressive limitation of one-body collective gates, with the single-qubit exception made explicit.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 4, one-body-algebras

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF p.4, (21)–(22): the u(1) collective-X and su(2) collective-X,Y
representations, stated as their exact matrix spans and real dimensions. -/
theorem oneBody_algebras {n : ℕ} (hn : 1 ≤ n) :
    (generatedSkewLie (generators1 n)).toSubmodule =
      Submodule.span ℝ {Complex.I • symmetricPauli n 1 0 0} ∧
    Module.finrank ℝ (generatedSkewLie (generators1 n)) = 1 ∧
    (generatedSkewLie (generators1XY n)).toSubmodule =
      Submodule.span ℝ {Complex.I • symmetricPauli n 1 0 0,
        Complex.I • symmetricPauli n 0 1 0, Complex.I • symmetricPauli n 0 0 1} ∧
    Module.finrank ℝ (generatedSkewLie (generators1XY n)) = 3 ∧
    (n = 1 → IsEquivariantlyUniversal (generatedSkewLie (generators1XY n)).toSubmodule) ∧
    (2 ≤ n →
      ¬ IsSubspaceControllable (generatedSkewLie (generators1 n)).toSubmodule ∧
      ¬ IsSubspaceControllable (generatedSkewLie (generators1XY n)).toSubmodule) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
