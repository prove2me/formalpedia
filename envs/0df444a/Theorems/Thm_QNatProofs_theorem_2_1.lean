-- Prove2me | Theorems.Thm_QNatProofs_theorem_2_1
-- name    : QNatProofs.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:04:50.704338+00:00
-- url     : https://prove2.me/theorems/f77894a2-0069-4a5c-b6b6-95bdb3904598
-- title:
--   Theorem 2.1 — quantum natural-proofs barrier
-- statement:
--   Let $\mathcal C$ be a quantum circuit model and $\varepsilon:\mathbb N\to\mathbb R$. If a PRAL family $\{D_{n,\lambda,T}\}$ is efficiently $\varepsilon$-approximately $\mathcal C$-preparable, then there is no natural promise property that is $\varepsilon$-useful against $\mathcal C_{\mathrm{poly}}$.
--
--   This reduces the barrier to constructing a preparable PRAL family, which §3–§4 do for the magic hierarchy.
--
--   Differences from the source:
--   - generalization: ε : ℕ → [0,1) → ε : ℕ → ℝ; reason: nothing in the proof uses ε < 1; the paper's own ε(n) = e^{−n} equals 1 at n = 0
--   - encoding: a quantum circuit model C → any gate set S and, for every number of wires, a set of circuits over S (CircuitClass S); reason: a circuit model specifies the allowed circuits; the theorem holds for every such class
--   - generalization: P^yes_n is Haar-measurable → NullMeasurableSet (measurable for the completion of Haar_n); reason: every Borel set qualifies, so more properties are natural and the non-existence statement is stronger
--   - encoding: probability over ψ ← D and the coins of A; A probabilistic polynomial time → Σ_s D{al_T = s}·Pr_coins[A(1^n,1^λ,s) = 1] over the strings s of length T·2^{n+1}; A a CoinAlg with polynomially many coins and one polynomial-time FinTM2 machine (IsPPT), input 1^n0 1^λ0 s; reason: al_T takes finitely many values; a finite sum avoids integrals of possibly non-measurable functions
--   - encoding: a designated n-qubit output register; the other qubits traced out → the first n wires; the partial trace over the remaining wires (reducedOutput); reason: any designation is a renaming of wires, which changes neither size nor level
--   - reading: al_T(ψ): polar coordinates written to T fractional bits → QNatProofs.al: basis strings in increasing binary order, r-bits then θ-bits, truncation ⌊2^T r⌋ capped at 2^T−1 (so r = 1 is written 1⋯1), θ = arg/(2π) mod 1 with θ(0) = 0; reason: the printed codomain {0,1}^{2T·2^n} forces the cap; the order and θ(0) are unspecified on p.8
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Theorem 2.1, p.10; proof p.10

import Mathlib
import Definitions.Def_QNatProofs_IsPRAL

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms

/-- **Theorem 2.1 (Quantum natural-proofs barrier)** (Li, Parham, *Natural proofs for quantum
state preparation lower bounds*, arXiv:2610.06826 (held copy sha256 b604fa11…), p.10): "Let `C` be a
quantum circuit model and let `ε : ℕ → [0, 1)`. Suppose there exists a PRAL family `{D_{n,λ,T}}`
that is efficiently `ε`-approximate `C`-preparable. Then there are no natural promise properties
that are `ε`-useful against `C_poly`."

**Formalization Note** A circuit model is any gate set `S` with any set of circuits over it for
each number of wires; `ε` is any real function (the paper's own use, `ε(n) = e^{-n}`, equals `1`
at `n = 0`). -/
theorem theorem_2_1 {S : Set Gate} (C : CircuitClass S) (ε : ℕ → ℝ) (𝒟 : PRALFamilyData)
    (hPRAL : IsPRAL 𝒟) (hprep : EffApproxPreparable 𝒟 C ε) :
    ¬ ∃ P : PromiseProperty, P.IsNatural ∧ P.IsUseful C ε := by sorry

end QNatProofs
