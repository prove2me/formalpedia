-- Prove2me | Theorems.Thm_RobustQSC_acceptance_probability_eq_trace_accOp
-- name    : RobustQSC.acceptance_probability_eq_trace_accOp
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:56:49.657199+00:00
-- url     : https://prove2.me/theorems/ef57af25-541f-45d9-86f0-1d2e1b08acc1
-- title:
--   §4, p.20 — Protocol 1 accepts with probability $\mathrm{Tr}[A\rho]$
-- statement:
--   Let $n\ge1$. For a target state $|\psi\rangle$ and a lab state $\rho$, the probability that Protocol 1 accepts equals
--
--   $$
--   \mathrm{Tr}[A\rho],
--   $$
--
--   where $A$ is the acceptance operator of the target. This identity converts the protocol into a single operator, on which every later statement is made.
--
--   Differences from the source:
--   - generalization: a target state and a lab state → every vector $\psi$ and every complex matrix $\rho$; reason: both sides are linear in $\rho$ and the zero-fibre convention covers every $\psi$; unit vectors and density matrices are a special case
--   - reading: Step 4 of Protocol 1 and the normalization in $A$ on an outcome with zero post-measurement vector (undefined) → reject, and the term of $A$ is $0$; reason: the only convention under which the identity holds for every target; it is null for a Haar-random target
--   - encoding: $z\in\{0,1\}^{n-1}$ on $[n]\setminus i$ → $x\in\{0,1\}^n$ with $x_i=0$; reason: Lean convention; same operator
--   - encoding: $n$ qubits with a holdout qubit $j\in[n]$ → hypothesis $n\ge1$; reason: Protocol 1 samples $j\in[n]$, which needs $n\ge1$
--   - encoding: $\mathrm{Tr}[A\rho]$ → `effectProb (accOp ψ) ρ`, the real part of $\mathrm{Tr}(A\rho)$; reason: $A$ is Hermitian, so the trace is real on Hermitian $\rho$; the acceptance probability is real
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), §4, p.20

import Definitions.Def_RobustQSC_protocol1
import Definitions.Def_RobustQSC_accOp

namespace RobustQSC

open QAlgorithms

/-- **§4, acceptance operator (p.20).** For a target state `|ψ⟩` and a lab state `ρ`, the
acceptance probability of Protocol 1 is `Tr[Aρ]`, where `A` is the operator of the p.20 display
(`accOp ψ`).

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), §4, p.20 ("we can rewrite the acceptance probability in Protocol 1 as Tr[Aρ] where
A is the following PSD operator").

**Formalization Note.** Stated for every vector `ψ` and every matrix `ρ` (both sides are linear
in `ρ`); `n ≥ 1` so that a holdout qubit exists. Zero fibers: both the protocol and `accOp`
give acceptance `0` on an outcome of probability `0` on `|ψ⟩`. -/
theorem acceptance_probability_eq_trace_accOp (n : ℕ) (hn : 1 ≤ n)
    (ψ : EuclideanSpace ℂ (Qubits n)) (ρ : Matrix (Qubits n) (Qubits n) ℂ) :
    (protocol1 n).outProb ψ ρ true = effectProb (accOp ψ) ρ := by sorry

end RobustQSC
