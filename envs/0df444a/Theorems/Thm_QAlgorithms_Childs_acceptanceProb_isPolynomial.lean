-- Prove2me | Theorems.Thm_QAlgorithms_Childs_acceptanceProb_isPolynomial
-- name    : QAlgorithms.Childs.acceptanceProb_isPolynomial
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:33:04.856564+00:00
-- url     : https://prove2.me/theorems/54ab7deb-1981-4c24-8e39-e61c5540c4ae
-- title:
--   Polynomial method: the acceptance probability of a t-query algorithm is a polynomial of degree at most 2t
-- statement:
--   This is the basic lemma of the polynomial method (Beals, Buhrman, Cleve, Mosca, de Wolf).
--
--   Fix $n, t \in \mathbb N$ and a finite workspace $W$. A $t$-query quantum algorithm acts on the Hilbert space spanned by $|i, b, w\rangle$ with $i \in \{1, \dots, n\}$, $b \in \{0,1\}$ and $w \in W$. It is given by a unit start state $|\psi\rangle$ and unitaries $U_0, U_1, \dots, U_t$, none of which depends on the input. On a black-box input $x \in \{0,1\}^n$ the algorithm prepares
--
--   $$
--   |\psi_x^t\rangle = U_t (O_x \otimes I_W) U_{t-1} \cdots U_1 (O_x \otimes I_W) U_0 |\psi\rangle,
--   $$
--
--   where $O_x$ is the phase oracle $O_x |i, b\rangle = (-1)^{b x_i} |i, b\rangle$. The algorithm accepts if measuring $|\psi_x^t\rangle$ in the computational basis gives an outcome in a fixed set $\mathrm{Acc}$ of basis states. Then there is a real polynomial $p \in \mathbb R[x_1, \dots, x_n]$ of total degree at most $2t$ such that, for every $x \in \{0,1\}^n$,
--
--   $$
--   p(x_1, \dots, x_n) = \sum_{z \in \mathrm{Acc}} \bigl|\langle z | \psi_x^t \rangle\bigr|^2 .
--   $$
--
--   The lemma turns query lower bounds into lower bounds on the degree (or approximate degree) of polynomials that represent the function being computed.
--
--   **Formalization Note** The source's state (21.1) has no unitary before the first query. The extra $U_0$ changes nothing, because $U_0|\psi\rangle$ is again an arbitrary input-independent unit vector, and $U_0 = I$ recovers (21.1) exactly. The oracle is the phase form (21.3), which is the form the proof uses. The polynomial is evaluated at the 0/1 point determined by $x$.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 106, Lemma 21.1. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Polynomial
set_option autoImplicit false

namespace QAlgorithms.Childs

/-- **Childs, Lemma 21.1** (PDF p. 106; model §21.1, p. 105, and §21.2, (21.1), (21.3), p. 106).
The acceptance probability of a `t`-query quantum algorithm for a problem with black-box input
`x ∈ {0,1}^n` is a polynomial in `x_1, …, x_n` of degree at most `2t`.

The algorithm is a `QueryAlg (Fin n) Bool W t`: an `x`-independent unit start state on the query
register `|i, b⟩` (`i ∈ [n]`, `b ∈ {0,1}`) and a workspace `W`, and `x`-independent unitaries
`U_0, …, U_t`, with the oracle `O_x ⊗ I_W` between consecutive unitaries. The oracle is the phase
oracle (21.3) `O_x |i, b⟩ = (−1)^{b x_i} |i, b⟩` (`controlledPhaseOracle x`), the form the proof
uses in (21.6). The source's (21.1) has no unitary before the first query; the extra `U_0` changes
nothing, since `U_0 |ψ⟩` is again an arbitrary `x`-independent unit vector (take `U_0 = I` to
recover (21.1) exactly). Acceptance is a computational-basis measurement of the final state with
outcome in an arbitrary set `Acc` of basis states (the proof: "the probability of any basis state
(and hence the probability of success)"). The polynomial is chosen after the algorithm and `Acc`,
and the identity is required at every 0/1 point `x`. -/
theorem acceptanceProb_isPolynomial (n t : ℕ) {W : Type*} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Fin n) Bool W t) (Acc : Finset ((Fin n × Bool) × W)) :
    ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ x : Fin n → Bool,
        MvPolynomial.eval (boolPoint x) p =
          probEvent (A.finalState (controlledPhaseOracle x)) fun z => z ∈ Acc := by
  sorry


end QAlgorithms.Childs
