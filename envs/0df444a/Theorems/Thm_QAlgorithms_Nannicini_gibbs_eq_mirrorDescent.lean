-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_gibbs_eq_mirrorDescent
-- name    : QAlgorithms.Nannicini.gibbs_eq_mirrorDescent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:53:09.77497+00:00
-- url     : https://prove2.me/theorems/ae336594-d31e-42d6-9c8a-d9c6f24b0cb2
-- title:
--   Entropic mirror descent iterates are the Gibbs states of the accumulated subgradients
-- statement:
--   Let $n \ge 1$, let $\eta \in \mathbb{R}$ be a step size, and let $G^{(1)}, G^{(2)}, \dots$ be Hermitian $n \times n$ matrices (the subgradients). Define Hermitian matrices $H^{(t)}$ by
--
--   $$
--   H^{(1)} = 0_{n\times n}, \qquad H^{(t+1)} = H^{(t)} - \eta G^{(t)} \quad (t \ge 1),
--   $$
--
--   and the Gibbs states $\rho^{(t)} := \exp(H^{(t)}) / \operatorname{Tr}\exp(H^{(t)})$.
--
--   Mirror descent with the von Neumann negative entropy $h(\rho) = \operatorname{Tr}(\rho\log\rho - \rho)$ as mirror map over the set $S^n_{+,1}$ of density matrices, started at $I/n$, is the recursion (Eq. (8.8))
--
--   $$
--   \rho^{(1)} = \frac{I}{n}, \qquad \rho^{(t+1)} \in \operatorname*{arg\,min}_{\sigma \in S^n_{+,1}} D\bigl(\sigma \,\big\|\, \exp(\log\rho^{(t)} - \eta G^{(t)})\bigr),
--   $$
--
--   where $D(\rho\|\sigma) = \operatorname{Tr}(\rho\log\rho - \rho\log\sigma - \rho + \sigma)$ is the quantum relative entropy. Then:
--
--   1. the sequence of Gibbs states $(\rho^{(t)})_{t\ge1}$ satisfies this recursion;
--   2. every sequence satisfying this recursion coincides with $(\rho^{(t)})_{t \ge 1}$.
--
--   This identifies entropic mirror descent on density matrices with the matrix multiplicative weights update, whose iterates are Gibbs states that a quantum computer can prepare.
--
--   **Formalization Note** The argmin is encoded through the relative entropy itself (Eq. (8.8)), not through the explicit solution (8.9), so the statement is not definitional. Matrix logarithm and $x\log x$ use the continuous functional calculus. The hypothesis $n \ge 1$ is needed for density matrices to exist.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 182, Proposition 8.7. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Nannicini_Ch08a_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms.SDP

open scoped ComplexOrder

/-- Nannicini pp.182–183, Proposition 8.7. Let `G^(1), G^(2), …` be Hermitian `n × n` matrices
(`n ≥ 1`), `η ∈ ℝ`, and let `H^(1) = 0`, `H^(t+1) = H^(t) − η G^(t)`. Then the Gibbs states
`ρ^(t) = exp(H^(t)) / Tr exp(H^(t))` coincide with the iterates of mirror descent with the von
Neumann negative entropy as mirror map and initial point `I/n` (Eq. (8.8): `ρ^(t+1)` minimizes the
quantum relative entropy `D(·‖exp(log ρ^(t) − ηG^(t)))` over the density matrices). Both
directions: the Gibbs sequence satisfies this recursion, and every sequence satisfying it equals
the Gibbs sequence at every `t ≥ 1`. -/
theorem gibbs_eq_mirrorDescent {n : ℕ} (hn : 0 < n) (η : ℝ)
    (G : ℕ → Matrix (Fin n) (Fin n) ℂ) (hG : ∀ t, (G t).IsHermitian)
    (H : ℕ → Matrix (Fin n) (Fin n) ℂ) (hH1 : H 1 = 0)
    (hHsucc : ∀ t ≥ 1, H (t + 1) = H t - (η : ℂ) • G t) :
    IsEntropicMirrorDescent η G (fun t => gibbsState (H t)) ∧
      ∀ ρ : ℕ → Matrix (Fin n) (Fin n) ℂ, IsEntropicMirrorDescent η G ρ →
        ∀ t ≥ 1, ρ t = gibbsState (H t) := by
  sorry








end QAlgorithms.Nannicini
