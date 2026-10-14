-- Prove2me | Theorems.Thm_QAlgorithms_Childs_kutin_average_isPolynomial
-- name    : QAlgorithms.Childs.kutin_average_isPolynomial
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:32:55.907988+00:00
-- url     : https://prove2.me/theorems/c65762c1-64cd-4ce4-991f-d0e08b40e585
-- title:
--   Kutin's lemma: the permutation-averaged polynomial is a polynomial in (m, a, b)
-- statement:
--   This is Kutin's symmetrization lemma for the collision problem.
--
--   Fix $n \ge 0$ and consider strings $x \in [n]^n$, $[n] = \{1,\dots,n\}$, encoded by the indicator variables $\delta_{ij} = 1$ if $x_i = j$ and $0$ otherwise ($i, j \in [n]$). A triple $(m,a,b)$ of natural numbers is *valid* if $m \in \{0,\dots,n\}$, $a, b \ge 1$, $a \mid m$ and $b \mid n-m$. For a valid triple define the string
--
--   $$
--   x^{m,a,b}_i = \begin{cases} \lceil i/a \rceil & 1 \le i \le m,\\ n - \lfloor (n-i)/b \rfloor & m < i \le n, \end{cases}
--   $$
--
--   which is $a$-to-one on its first $m$ positions and $b$-to-one on the rest. For permutations $\sigma, \tau$ of $[n]$ let $x^{\sigma\tau}_i = \tau(x^{m,a,b}_{\sigma(i)})$ and let $\delta^{\sigma\tau}_{ij}$ be its indicator variables.
--
--   Let $p$ be any real polynomial in the $n^2$ variables $\delta_{ij}$, and for a valid triple set
--
--   $$
--   P(m,a,b) = \mathbb{E}_{\sigma,\tau}\bigl[p(\{\delta^{\sigma\tau}_{ij}\})\bigr] = \frac{1}{(n!)^2} \sum_{\sigma,\tau \in S_n} p(\{\delta^{\sigma\tau}_{ij}\}).
--   $$
--
--   Then there is a real polynomial $Q(m,a,b)$ in three variables with $\deg Q \le \deg p$ (total degrees) such that
--
--   $$
--   Q(m,a,b) = P(m,a,b) \quad \text{for every valid triple } (m,a,b).
--   $$
--
--   Applied to the acceptance probability of a $t$-query algorithm (a polynomial of degree at most $2t$ in the $\delta_{ij}$), this reduces the collision lower bound to degree bounds for a polynomial in three integer variables, to which Paturi's lemma is applied.
--
--   **Formalization Note** Indices and values are 0-based in Lean (`Fin n`); the defining formulas of $x^{m,a,b}$ are kept in 1-based form and the value is shifted by one. The polynomial $p$ is an arbitrary `MvPolynomial (Fin n × Fin n) ℝ`, not necessarily multilinear, and degrees are total degrees.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 113, Lemma 22.1. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Polynomial
set_option autoImplicit false

namespace QAlgorithms.Childs

/-- **Childs, Lemma 22.1** (Kutin; PDF p. 113, with the setting of §22.1, p. 111, (22.3), p. 112,
and §22.5, (22.6)–(22.7), p. 113). Let `p({δ_ij})` be a polynomial in the variables `δ_ij`,
`i, j ∈ {1, …, n}`. For a valid triple `(m, a, b)` (`m ∈ {0, …, n}`, `a ∣ m`, `b ∣ n − m`, with
`a, b ≥ 1` since they are the multiplicities of the `a`-to-one and `b`-to-one parts:
`ValidKutinTriple n m a b`), let `P(m, a, b) := E_{σ,τ}[p({δ^{στ}_ij})]`, the average over all
pairs of permutations `σ, τ` of `{1, …, n}` of `p` evaluated at the indicator variables of the
input `x^{στ}_i = τ(x^{m,a,b}_{σ(i)})` (`kutinAverage p m a b`). Then `P` is a polynomial in
`m, a, b` with `deg P ≤ deg p`.

"`P` is a polynomial" is read as: there is a real trivariate polynomial `Q` of total degree at
most the total degree of `p` with `Q(m, a, b) = P(m, a, b)` at every valid triple (the domain on
which `P` is defined). Indices are 0-based in Lean (`Fin n`); `kutinInput` keeps the source's
1-based formulas `⌈i/a⌉` and `n − ⌊(n − i)/b⌋` and shifts the value by one. `p` is an arbitrary
polynomial (not necessarily multilinear), as in the source. -/
theorem kutin_average_isPolynomial (n : ℕ) (p : MvPolynomial (Fin n × Fin n) ℝ) :
    ∃ Q : MvPolynomial (Fin 3) ℝ, Q.totalDegree ≤ p.totalDegree ∧
      ∀ m a b : ℕ, ValidKutinTriple n m a b →
        MvPolynomial.eval ![(m : ℝ), (a : ℝ), (b : ℝ)] Q = kutinAverage p m a b := by
  sorry

end QAlgorithms.Childs
