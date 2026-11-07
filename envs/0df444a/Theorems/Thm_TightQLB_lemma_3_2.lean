-- Prove2me | Theorems.Thm_TightQLB_lemma_3_2
-- name    : TightQLB.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:04:05.183632+00:00
-- url     : https://prove2.me/theorems/ed418429-5f34-4493-bfea-c0ef05e7cc5a
-- title:
--   Lemma 3.2 — reduction to a fixed sequence of controlled queries
-- statement:
--   Consider an experiment of Definition 3.1 with device register $A$, Eve register $E$ and initial state $\rho_{AE}$. There are a finite-dimensional register $A'$ containing the query register $\mathsf Q$ and a control qubit $\mathsf C$, a unit vector $\psi_0\in A'\otimes E$ whose reduced state on $E$ is $\rho_E$, oracle-independent unitaries $U_0,\dots,U_q$ on $A'$, and orthogonal projections $\{\Pi_z\}$ on $A'$ with $\sum_z\Pi_z=I$, such that with $V_\omega=U_qO^{\mathrm c}_\omega U_{q-1}\cdots U_1O^{\mathrm c}_\omega U_0$, for every oracle $\omega$ and every $z$,
--
--   $$
--   \rho^\omega_z=\operatorname{Tr}_{A'}\bigl[(\Pi_zV_\omega\otimes I_E)|\psi_0\rangle\langle\psi_0|(\Pi_zV_\omega\otimes I_E)^\dagger\bigr],\qquad\Pr[Z=z\mid\omega]=\|(\Pi_zV_\omega\otimes I_E)\psi_0\|^2 .
--   $$
--
--   This puts every device, however adaptive, into the unitary form on which the rest of the analysis works.
--
--   **Formalization Note** `A′` is `(C × Q) × Fin k` for some `k`, and $|v\rangle\langle v|$ is `Matrix.vecMulVec v (star v)`.
--
--   Differences from the source:
--   - reading: the operational experiment of Definition 3.1 (classical record, paths with at most q queries, ancillas, measurements, record-selected and record-controlled queries, output a function of the final record) → a density matrix on A × E, q + 1 oracle-independent CPTP maps on A, exactly q controlled queries on the fixed registers C × Q between them, and a POVM on A; reason: the proof of Lemma 3.2, Steps 1–2, puts every such experiment in this form, and conversely a CPTP map is an ancilla, a unitary and an ignored register and a POVM is a measurement of an ancilla, so the class is the same
--   - generalization: an oracle ω of either ensemble, with its unitary O_ω on a register Q of the corresponding type → every finite type Q and every matrix O : Matrix Q Q ℂ, unitary or not; reason: it specializes to Q = X × T, O = O_f and to Q = ℂ|⊥⟩ ⊕ ℂ^N, O = O_ϕ, and the statement is an algebraic identity that does not use unitarity of O
--   - generalization: "Throughout, n ≥ 1" (p. 13) → every n : ℕ, with no hypothesis on n; reason: the argument does not use n ≥ 1, and the instances with n ≥ 1 are the source's statement
--   - encoding: ρ^ω_z, the subnormalized state of E on the event Z = z → Tr_A[(M_z ⊗ I_E) ρ_final], and Pr[Z = z | ω] as the real part of its trace; reason: equal to Tr_A[(√M_z ⊗ I) ρ_final (√M_z ⊗ I)] by cyclicity on A
--   - encoding: "a finite-dimensional register A′, which contains a query register Q … and a control qubit C" → A′ = (C × Q) × Fin k for some k : ℕ; reason: every finite-dimensional complement of C × Q is a Fin k
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Lemma 3.2, pp. 15–16 (PDF pp. 18–19), Eqs. (14)–(16)

import Mathlib
import Definitions.Def_TightQLB_Experiment
import Definitions.Def_TightQLB_NormalForm
open QAlgorithms

namespace TightQLB

/-- **Lemma 3.2 (Reduction to a fixed sequence of controlled queries)**, pp.15–16 (PDF pp.18–19),
Eqs. (14)–(16).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

For every experiment of Definition 3.1 (in either ensemble) there are a register `A′` containing the
query register and a control qubit, a unit vector `ψ₀ ∈ A′ ⊗ E` whose reduced state on `E` is `ρ_E`, oracle-independent
unitaries `U₀, …, U_q` on `A′` and orthogonal projections `{Π_z}` with `Σ_z Π_z = I`, such that for
every oracle and every `z`,
`ρ^ω_z = Tr_{A′}[(Π_z V_ω ⊗ I_E)|ψ₀⟩⟨ψ₀|(Π_z V_ω ⊗ I_E)†]` and `Pr[Z = z | ω] = ‖(Π_z V_ω ⊗ I_E)ψ₀‖²`.

**Formalization Note.**
* The experiment is `TightQLB.Experiment` (Definition 3.1 in channel form) and the normal form is
  `TightQLB.NormalForm`, whose register is `A′ = (C × Q) × Fin k` for some `k`.
* The query register `Q` and the oracle matrix `O` are arbitrary: the Fourier ensemble is
  `Q = Qubits n × Bool`, `O = valueOracle fb`, and the Haar ensemble is `Q = C|⊥⟩ ⊕ ℂ^N`, `O = O_ϕ`.
  Unitarity of `O` is not assumed, since the identity does not use it.
* `|v⟩⟨v|` is `Matrix.vecMulVec v (star v)`; `ρ_E` is `Tr_A ρ_AE`.
* Nothing in the statement requires `n ≥ 1`. -/
theorem lemma_3_2 {n q : ℕ} {Q W E : Type} [Fintype Q] [DecidableEq Q] [Fintype W] [DecidableEq W]
    [Fintype E] [DecidableEq E] (A : Experiment n q Q W E) :
    ∃ (k : ℕ) (B : NormalForm n q Q (Fin k) E),
      WildeQIT.partialTraceLeft
          (Matrix.vecMulVec (WithLp.ofLp B.ψ₀) (star (WithLp.ofLp B.ψ₀))) =
        WildeQIT.partialTraceLeft A.ρ₀ ∧
      ∀ (O : Matrix Q Q ℂ) (z : Qubits n),
        A.eveState O z =
            WildeQIT.partialTraceLeft (Matrix.vecMulVec (WithLp.ofLp (B.branch O z))
              (star (WithLp.ofLp (B.branch O z)))) ∧
          A.outProb O z = ‖B.branch O z‖ ^ 2 := by sorry

end TightQLB
