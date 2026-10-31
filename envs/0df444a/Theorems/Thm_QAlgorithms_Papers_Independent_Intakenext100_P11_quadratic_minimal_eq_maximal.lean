-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P11_quadratic_minimal_eq_maximal
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P11.quadratic_minimal_eq_maximal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:40:36.725658+00:00
-- url     : https://prove2.me/theorems/e6794805-55c3-4276-a6c4-98e2110ad9f3
-- title:
--   Quadratic position–momentum operators: minimal and maximal realizations coincide
-- statement:
--   Let $d\geq 1$ be an integer and let $\mathcal H=L^2(\mathbb R^d;\mathbb C)$ with Lebesgue measure. Write $X_k f(x)=x_k f(x)$ and $P_k f=-i\partial_k f$. Fix arbitrary complex coefficients of an ordered polynomial $Q$ of total degree at most two in the operators $X_1,\ldots,X_d,P_1,\ldots,P_d$, including constant and linear terms. Let $Q_0$ denote this differential expression on $C_c^\infty(\mathbb R^d;\mathbb C)$. Define its maximal distributional graph by
--
--   $$
--   G_{\max}(Q)=\{(u,v)\in\mathcal H\times\mathcal H:Qu=v\text{ in distributions}\}.
--   $$
--
--   Then, with graph closure taken in $\mathcal H\times\mathcal H$,
--
--   $$
--   \overline{\operatorname{Graph}(Q_0)}=G_{\max}(Q).
--   $$
--
--   In particular, the closure has domain exactly those $u\in\mathcal H$ for which the distribution $Qu$ belongs to $\mathcal H$, and its value there is that distribution's $L^2$ representative. This identifies both the domain and the action of the closed realization used for the paper's quadratic generators.
--
--   **Formalization Note** Distributional equality is expressed by bilinear integration against every smooth compactly supported complex test function. The transpose reverses the order of generators and sends $-i\partial_k$ to $+i\partial_k$. Explicit integrability clauses guard the pairings; they impose no extra restriction on these $L^2$ pairs. No symmetry, positivity, or ellipticity is assumed.
-- source:
--   Quantum dynamical semigroups for diffusion models with Hartree interaction, arXiv:math-ph/0309052v2, PDF p. 8, Lemma 3.3; (3.8)–(3.9)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P11

noncomputable section

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakenext100.P11

/-- Lemma 3.3, Arnold--Sparber, arXiv:math-ph/0309052v2, PDF pp.8--9.
The closure of the C_c^∞ graph equals the maximal distributional L² graph,
including both the domain and the operator action. The bars over P in (3.9)
are present in the PDF but absent from the extracted text. -/
theorem quadratic_minimal_eq_maximal (d : ℕ) (hd : 0 < d)
    (P : QuadraticExpression d) :
    closure (initialQuadraticGraph P) = maximalQuadraticGraph P := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P11

end
