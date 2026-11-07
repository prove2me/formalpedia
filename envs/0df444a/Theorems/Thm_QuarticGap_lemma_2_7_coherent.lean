-- Prove2me | Theorems.Thm_QuarticGap_lemma_2_7_coherent
-- name    : QuarticGap.lemma_2_7_coherent
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:21.039272+00:00
-- url     : https://prove2.me/theorems/557e0fef-f529-42d8-8e52-274b5affe594
-- title:
--   Lemma 2.7, clause 2 — coherent access and $O_f$ implement each other with $O(1)$ calls
-- statement:
--   Let $\{A(f)\}$ be a family with known magnitudes. Every coherent input operation, its inverse and its controlled version can be implemented with $O(1)$ calls to $O_f|\sigma,c\rangle = |\sigma,c\oplus(1-f(\sigma))/2\rangle$ and fixed circuits. Conversely, if every point appears as some $\sigma_{ij}$, one call to $O_f$ can be implemented with two reversible entry queries. Quantum query complexities in the two models therefore agree up to constant factors:
--
--   1. every circuit with $Q$ coherent queries has a circuit with $O(Q)$ calls to $O_f$ and the same action, for a legal choice of the operations;
--   2. every circuit with $Q$ calls to $O_f$ has a circuit with $O(Q)$ coherent queries and the same action, for every legal choice of the operations.
--
--   **Formalization Note** The constants are absolute and the circuits are fixed before $f$. Ancillas start and end in $|0\rangle$. The encoding `enc` is any map that tells apart the values an entry takes, which is what a fixed binary encoding must provide. $A(f) \ne 0$ is the standing assumption of Definition 2.2.
--
--   Differences from the source:
--   - generalization: a family whose map (i, j) ↦ σ_ij is computed by a fixed reversible circuit → no such hypothesis; reason: the Lean circuits may use any unitary gate, so the map is one gate; every family of the source is covered
--   - encoding: matrices of size N₁ × N₂ → matrices indexed by d₁ and d₂ qubit registers; reason: any size fits on ⌈log N⌉ wires with zero rows and columns added
--   - reading: a fixed binary encoding → any map from reals to w bits; the converse assumes that it tells apart the values an entry takes; reason: an encoding of the entries must distinguish them
--   - encoding: Definition 2.2 is for a nonzero matrix → the hypothesis A f ≠ 0 for every f; reason: the standing assumption of Definition 2.2; for A = 0 norm preparation has no target state
--   - reading: quantum query complexities in the two models agree up to constant factors → two conjuncts: every circuit in one model has a circuit in the other with at most C times the queries that implements the same unitary with ancillas starting and ending in |0⟩; reason: this is agreement up to constant factors for every algorithm at once, with an absolute constant
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Lemma 2.7, preamble and clause 2, p.18

import Mathlib
import Definitions.Def_QuarticGap_IsCoherentAccess

open QAlgorithms

namespace QuarticGap

/-- Lemma 2.7, preamble and clause 2 (arXiv:2610.42069 (file sha256 9f68aaf9…), p.18). For a family
`{A(f)}` with known magnitudes, every coherent input operation, its inverse and its controlled version
can be implemented with `O(1)` calls to `O_f` and fixed circuits. Conversely, if every point appears as
some `σ_ij`, one call to `O_f` can be implemented with two reversible entry queries.

**Formalization Note** The first part: an absolute `C`, then for each family one set of circuits, fixed
before `f`, whose unitaries for each `f` are a legal choice of the operations. The second part holds for
every legal choice of the operations, and uses only the entry query. `μ_ij` and `σ_ij` are in
`IsKnownMagnitudeFamily`. Over `UnitaryGates` the map `(i, j) ↦ σ_ij` is computed by one gate, so the
source's reversible-circuit hypothesis is automatic. The encoding `enc` is any map that tells apart the
values an entry takes, which is what "fixed binary encoding" must provide for the converse. `A f ≠ 0`
is the standing assumption of Definition 2.2. The last two conjuncts are the source's closing
sentence, that quantum query complexities in the two models agree up to constant factors: each circuit
in one model has a circuit in the other with at most `C` times the queries and the same unitary on
wires whose ancillas start and end in `|0⟩`. -/
theorem lemma_2_7_coherent :
    (∃ C : ℕ, ∀ (m d₁ d₂ w : ℕ) (A : (Qubits m → ℤˣ) → Matrix (Qubits d₁) (Qubits d₂) ℝ),
      IsKnownMagnitudeFamily A → (∀ f, A f ≠ 0) → ∀ enc : ℝ → Qubits w,
      ∃ (N : ℕ) (sim : AccessSim (coherentArity d₁ d₂ w) (m + 1) N), sim.CallsAtMost C ∧
        ∀ f, ∃ orc, IsCoherentAccess (A f) (fun i j => enc (A f i j)) orc ∧
          sim.Realizes (bitOracle (signBit f)) orc) ∧
    (∀ (m d₁ d₂ w : ℕ) (A : (Qubits m → ℤˣ) → Matrix (Qubits d₁) (Qubits d₂) ℝ),
      IsKnownMagnitudeFamily A → (∀ f, A f ≠ 0) → ∀ enc : ℝ → Qubits w,
      (∀ f g i j, A f i j ≠ A g i j → enc (A f i j) ≠ enc (A g i j)) →
      (∀ σ, ∃ i j, ∃ μ : ℝ, μ ≠ 0 ∧ ∀ f, A f i j = μ * sgn (f σ)) →
      ∃ (N : ℕ) (c : OracleCircuit UnitaryGates (coherentArity d₁ d₂ w) (m + 1 + N)),
        c.queryCount 0 ≤ 2 ∧ (∀ k, k ≠ 0 → c.queryCount k = 0) ∧
        ∀ f orc, IsCoherentAccess (A f) (fun i j => enc (A f i j)) orc →
          ImplementsWithAncilla (c.unitary orc) (bitOracle (signBit f))) ∧
    (∃ C : ℕ, ∀ (m d₁ d₂ w : ℕ) (A : (Qubits m → ℤˣ) → Matrix (Qubits d₁) (Qubits d₂) ℝ),
      IsKnownMagnitudeFamily A → (∀ f, A f ≠ 0) → ∀ enc : ℝ → Qubits w,
      ∀ (N : ℕ) (alg : OracleCircuit UnitaryGates (coherentArity d₁ d₂ w) N),
      ∃ (t : ℕ) (alg' : OracleCircuit UnitaryGates (fun _ : Fin 1 => m + 1) (N + t)),
        totalQueries alg' ≤ C * totalQueries alg ∧
        ∀ f, ∃ orc, IsCoherentAccess (A f) (fun i j => enc (A f i j)) orc ∧
          ImplementsWithAncilla (alg'.unitary fun _ => bitOracle (signBit f)) (alg.unitary orc)) ∧
    (∃ C : ℕ, ∀ (m d₁ d₂ w : ℕ) (A : (Qubits m → ℤˣ) → Matrix (Qubits d₁) (Qubits d₂) ℝ),
      IsKnownMagnitudeFamily A → (∀ f, A f ≠ 0) → ∀ enc : ℝ → Qubits w,
      (∀ f g i j, A f i j ≠ A g i j → enc (A f i j) ≠ enc (A g i j)) →
      (∀ σ, ∃ i j, ∃ μ : ℝ, μ ≠ 0 ∧ ∀ f, A f i j = μ * sgn (f σ)) →
      ∀ (N : ℕ) (alg : OracleCircuit UnitaryGates (fun _ : Fin 1 => m + 1) N),
      ∃ (t : ℕ) (alg' : OracleCircuit UnitaryGates (coherentArity d₁ d₂ w) (N + t)),
        totalQueries alg' ≤ C * totalQueries alg ∧
        ∀ f orc, IsCoherentAccess (A f) (fun i j => enc (A f i j)) orc →
          ImplementsWithAncilla (alg'.unitary orc)
            (alg.unitary fun _ => bitOracle (signBit f))) := by sorry

end QuarticGap
