-- Prove2me | Theorems.Thm_QAlgorithms_Papers_GuptaHeODonnell25_certify_single_qubit_measurements
-- name    : QAlgorithms.Papers.GuptaHeODonnell25.certify_single_qubit_measurements
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:13:55.638915+00:00
-- url     : https://prove2.me/theorems/adeb443c-c09b-4f53-941b-84922e9aadee
-- title:
--   Gupta–He–O'Donnell Theorem 1: one-copy certification of any pure state with adaptive single-qubit measurements
-- statement:
--   This is the one-copy certification theorem of Gupta, He and O'Donnell.
--
--   **Access model.** For $n\ge 1$ qubits, the algorithm accesses a pure hypothesis state $|\mathrm{hyp}\rangle\in(\mathbb C^2)^{\otimes n}$, $\||\mathrm{hyp}\rangle\|=1$, only through queries of Definition 15: for single-qubit projectors $\Pi_1,\dots,\Pi_n$ on $\mathbb C^2$ (each $\Pi_k=\Pi_k^\dagger=\Pi_k^2$, the identity allowed), the query returns $\langle\mathrm{hyp}|\Pi_1\otimes\cdots\otimes\Pi_n|\mathrm{hyp}\rangle$. It also flips fair coins, and it touches its single copy of the unknown $n$-qubit mixed state $\rho_{\mathrm{lab}}$ (positive semidefinite, trace one) only by projective measurements of one qubit at a time in an orthonormal basis $\{U|0\rangle,U|1\rangle\}$; the qubit, the basis, the queries and the coins may all depend adaptively on everything seen so far.
--
--   **Theorem.** There exist such an algorithm $\mathcal A_n$ for every $n$ and a constant $C$, chosen before $|\mathrm{hyp}\rangle$ and $\rho_{\mathrm{lab}}$, such that for every $n\ge1$, every run of $\mathcal A_n$ makes at most $C n$ query, coin and measurement steps, and for every $|\mathrm{hyp}\rangle$ and $\rho_{\mathrm{lab}}$, writing $\mathrm{Fid}=\langle\mathrm{hyp}|\rho_{\mathrm{lab}}|\mathrm{hyp}\rangle$,
--
--   $$
--   \Pr[\mathcal A_n\text{ outputs Accept}]\ge \mathrm{Fid},\qquad \Pr[\mathcal A_n\text{ outputs Reject}]\ge \frac{1-\mathrm{Fid}}{n}.
--   $$
--
--   Repeating this test $O(n\varepsilon^{-1}\ln(1/\delta))$ times and applying a Chernoff bound gives the paper's Main Theorem: certification of every pure state with $O(n^2)$ single-qubit measurements on $O(n)$ copies.
--
--   **Formalization Note** The output probability is computed on subnormalized post-measurement states (Lüders rule without renormalization). The running time is modelled by the number of query, coin and measurement steps on every execution path; classical post-processing between steps is not charged, which matches the source's $O(1)$ per-step cost only up to this modelling choice.
-- source:
--   Few Single-Qubit Measurements Suffice to Certify Any Quantum State (Gupta, He, O'Donnell), arXiv:2506.11355v2, Theorem 1, PDF p. 2. https://arxiv.org/abs/2506.11355v2 . PDF SHA-256: 542ce697a8cbe3fd6233e6bacdc0363fa9dc8b13aa2ec9af9f45bde2d83fa98b.

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
set_option autoImplicit false

namespace QAlgorithms.Papers.GuptaHeODonnell25

open QAlgorithms

/-- GHO Theorem 1 (p.2; proof §§2.2–2.4, pp.4–8). There exists an algorithm that given oracle
access to the classical description of a pure state `|hyp⟩` via the model in Definition 15 (p.8)
and one copy of a mixed state `ρ_lab`, makes only single-qubit measurements to `ρ_lab` and outputs
Accept with probability at least `Fid := ⟨hyp|ρ_lab|hyp⟩` and Reject with probability at least
`(1 − Fid)/n`. Moreover, the algorithm runs in time linear in the number of measurements.

Formalized: there is one family of algorithms `alg n` (`n` the number of qubits) and a constant
`C`, both chosen before `|hyp⟩` and `ρ_lab`, such that for every `n ≥ 1` every execution path of
`alg n` has at most `C · n` query, coin and measurement steps (the source's algorithm makes `n`
single-qubit measurements and runs in time `O(n)`, §2.4, p.8), and for every unit vector `|hyp⟩`
and every density matrix `ρ_lab` on `n` qubits, Accept has probability `≥ ⟨hyp|ρ_lab|hyp⟩` and
Reject has probability `≥ (1 − ⟨hyp|ρ_lab|hyp⟩)/n`. The fidelity is written
`Re Tr(|hyp⟩⟨hyp| ρ_lab) = ⟨hyp|ρ_lab|hyp⟩`. Classical post-processing between steps is not
charged (the continuations are arbitrary functions of the answers). -/
theorem certify_single_qubit_measurements :
    ∃ (alg : (n : ℕ) → SQCertAlg n) (C : ℕ),
      ∀ n : ℕ, 1 ≤ n →
        (alg n).StepsAtMost (C * n) ∧
        ∀ (hyp : EuclideanSpace ℂ (Qubits n)) (ρlab : Matrix (Qubits n) (Qubits n) ℂ),
          IsState hyp → IsDensityMatrix ρlab →
            (alg n).outProb hyp ρlab true ≥ effectProb (pureDensity hyp) ρlab ∧
            (alg n).outProb hyp ρlab false ≥ (1 - effectProb (pureDensity hyp) ρlab) / n := by
  sorry

end QAlgorithms.Papers.GuptaHeODonnell25
