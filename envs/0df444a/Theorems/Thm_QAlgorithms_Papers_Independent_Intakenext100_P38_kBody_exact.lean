-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_kBody_exact
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.kBody_exact
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:36:36.153724+00:00
-- url     : https://prove2.me/theorems/7e6036fc-8579-42ed-9b17-50418d07989f
-- title:
--   Theorem 5: exact k-body algebra
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Write $\mathfrak u_n$ for the skew-Hermitian commutant of the qubit-permuting representation of $S_n$, $\mathfrak s_n$ for its total-trace-zero subalgebra, and $\mathfrak d_n=[\mathfrak u_n,\mathfrak u_n]$ for its derived algebra, equivalently the algebra with independently traceless multiplicity blocks.
--
--   For $2\le k\le n$, let $G_k=\{P_{100},P_{010}\}\cup\{P_{00j}:2\le j\le k\}$ and $\mathfrak g_k=\operatorname{Lie}_{\mathbb R}\{iH:H\in G_k\}$.
--
--   For $0\le2\mu\le n$, define
--   $$C_\mu=\sum_{a+b+c=\mu}\frac{(2a)!(2b)!(2c)!}{a!b!c!}P_{2a,2b,2c}.$$
--   In particular $C_0=I$.
--
--   For real coefficients $c_{xyz}$ on the valid triples $x+y+z\le n$, put
--   $$M(c)=i\sum_{x+y+z\le n}c_{xyz}P_{xyz},\qquad \ell_\mu(c)=\sum_{a+b+c=\mu}\frac{c_{2a,2b,2c}}{a!b!c!}.$$
--
--   Let $Z_k=\operatorname{span}_{\mathbb R}\{iC_1,\ldots,iC_{\lfloor k/2\rfloor}\}$. Then
--   $$\mathfrak g_k=\mathfrak d_n+Z_k,\qquad Z_k\subseteq\mathfrak z(\mathfrak u_n),\qquad \dim Z_k=\lfloor k/2\rfloor.$$
--   Furthermore, if $\ell_\mu(c)=0$ for $\mu=0$ and for every $\lfloor k/2\rfloor<\mu\le\lfloor n/2\rfloor$, then $M(c)\in\mathfrak g_k$.
--
--   This identifies every generated central direction and retains the extra coefficient clause of the supplementary theorem on page 20. The $k=2$ boundary is the previously established two-body case.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 6, theorem5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.6,20–21, Theorem 5: exact central span, its dimension and centrality,
and the additional 'Furthermore' coefficient-sufficiency clause (E3)–(E4). -/
theorem kBody_exact {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    (gK n k).toSubmodule = centerlessSymmetricAlgebra n ⊔ centralSpan n (k / 2) ∧
    centralSpan n (k / 2) ≤ algebraCenter (symmetricUnitaryAlgebra n) ∧
    Module.finrank ℝ (centralSpan n (k / 2)) = k / 2 ∧
    (∀ c : ℕ → ℕ → ℕ → ℝ,
      (∀ mu : ℕ, 2 * mu ≤ n → (mu = 0 ∨ k / 2 < mu) →
        centralCoefficient c mu = 0) → coefficientCombination n c ∈ gK n k) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
