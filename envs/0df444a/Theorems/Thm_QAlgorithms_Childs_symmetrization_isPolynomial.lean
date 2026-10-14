-- Prove2me | Theorems.Thm_QAlgorithms_Childs_symmetrization_isPolynomial
-- name    : QAlgorithms.Childs.symmetrization_isPolynomial
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:33:07.664927+00:00
-- url     : https://prove2.me/theorems/08a07f71-934c-4316-8386-0153b49906f6
-- title:
--   Symmetrization: the Hamming-weight average of a multilinear polynomial is a polynomial of no larger degree
-- statement:
--   This is the symmetrization lemma of Minsky and Papert.
--
--   Let $p \in \mathbb R[x_1, \dots, x_n]$ be multilinear, meaning that every variable has degree at most $1$ in $p$. For $k \in \{0, 1, \dots, n\}$, let
--
--   $$
--   P(k) := \mathbb E_{|x| = k}\,[p(x)] = \binom{n}{k}^{-1} \sum_{x \in \{0,1\}^n,\ |x| = k} p(x),
--   $$
--
--   where $|x|$ is the Hamming weight of $x$ (its number of 1s). Then there is a univariate polynomial $Q \in \mathbb R[k]$ with $\deg Q \le \deg p$ (total degree) such that $Q(k) = P(k)$ for every $k \in \{0, 1, \dots, n\}$.
--
--   Symmetrization reduces questions about multivariate polynomials that represent symmetric Boolean functions, such as parity or OR, to questions about univariate polynomials. Those questions can then be settled by counting sign changes or by Markov's inequality.
--
--   **Formalization Note** The statement that "$P$ is a polynomial" is formalized as agreement with a univariate polynomial on the points $\{0, \dots, n\}$, the only points where $P$ is defined. For these $k$ the average is taken over a nonempty set.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 107, Lemma 21.2. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Polynomial
set_option autoImplicit false

namespace QAlgorithms.Childs


/-- **Childs, Lemma 21.2** (PDF p. 107). Given any `n`-variate multilinear polynomial `p`, let
`P(k) := E_{|x|=k}[p(x)]`, the average of `p` over the bit strings of Hamming weight `k`
(`weightAverage p k`), for `k ∈ {0, …, n}`. Then `P` is a polynomial with `deg P ≤ deg p`.

"`P` is a polynomial" is read as: there is a univariate real polynomial `Q` of degree at most the
total degree of `p` with `Q(k) = P(k)` for every `k ∈ {0, …, n}` (the domain on which `P` is
defined; for these `k` the average is over a nonempty set). -/
theorem symmetrization_isPolynomial (n : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) :
    ∃ Q : Polynomial ℝ, Q.natDegree ≤ p.totalDegree ∧
      ∀ k : ℕ, k ≤ n → Q.eval (k : ℝ) = weightAverage p k := by
  sorry

end QAlgorithms.Childs
