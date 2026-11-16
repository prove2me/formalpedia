-- Prove2me | Theorems.Thm_StabTestMem_Supplement_optimal_learning_bounds
-- name    : StabTestMem.Supplement.optimal_learning_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:42:41.056257+00:00
-- url     : https://prove2.me/theorems/0a3584dd-2c5b-422c-998b-fc5a883f3c08
-- title:
--   Theorem 1.2 — optimal learning bounds: $\Theta(n^2/k)$ copies for non-adaptive learning of stabilizer states with $k$ qubits of memory (corrected: $n^2/\min(k,n)$ copies, $k\ge1$)
-- statement:
--   This is the learning counterpart of the mission's testing theorem: with $k$ qubits of memory, non-adaptive learning of an $n$-qubit stabilizer state takes $\Theta(n^2/k)$ copies.
--
--   A learner receives copies of an unknown $n$-qubit state one at a time, carries a quantum memory of $k$ qubits between rounds, and is **non-adaptive**: its random choices are made in advance and the operation of each round does not depend on earlier outcomes; the output is computed from the transcript afterwards. It **learns** $|\psi\rangle$ if it outputs a unit vector equal to $|\psi\rangle$ up to a global phase.
--
--   1. *(Upper bound.)* There is an absolute constant $C$ such that for all $n\ge1$ and $k\ge1$ some non-adaptive learner with $k$ qubits of memory, using
--   $$t\le C\,\frac{n^2}{\min(k,n)}$$
--   copies, learns every $n$-qubit stabilizer state with probability at least $2/3$.
--   2. *(Lower bound.)* There are constants $c>0$ and $n_0$ such that for all $n\ge n_0$ and $k\ge1$, every non-adaptive learner with $k$ qubits of memory that learns every $n$-qubit stabilizer state with probability at least $2/3$ uses
--   $$t\ge c\,\frac{n^2}{k}$$
--   copies.
--
--   For $1\le k\le n$ the two bounds match. At $k=n$ (two-copy measurements) $\Theta(n)$ copies are necessary and sufficient, and at $k=1$ the bound is $\Theta(n^2)$, below the $O(n^3)$ of the known single-copy learners.
--
--   **Formalization Note** Learners are `StabTestMem.Supplement.NALearner` (precommitted randomness, then non-adaptive protocols of the published `StabTestMem.MemProtocol` with exactly $k$ memory qubits); stabilizer states are the published `QAlgorithms.IsStabilizerState`.
--
--   Differences from the source:
--   - correction: O(n^2/k) copies for every k ≥ 1 → t ≤ C·n²/min(k, n) for every k ≥ 1; reason: the printed bound is false for large k: at n = 1 and k > C it forces t = 0, a 0-copy learner outputs a law independent of ψ, and the six one-qubit stabilizer states are pairwise distinct up to phase, so one of them is learned with probability ≤ 1/6; the proof (blocks of size ≤ k, ⌈n/k⌉ blocks, p. 53, and "O(n) ≤ O(n^2/k) for k ≤ n", p. 55) gives n²/min(k, n), which equals the printed bound for k ≤ n, the paper's stated range (p. 5)
--   - reading: non-adaptive protocol → NALearner: a precommitted random seed, then for each seed a protocol whose instruments do not depend on the outcome history, then classical post-processing; reason: §6.1 (pp. 52, 55) precommits random Clifford branches before any outcome; the same reading is used in both halves
--   - reading: Ω(n^2/k) → ∃ c > 0, ∃ n₀, ∀ n ≥ n₀: c·n²/k ≤ t; reason: asymptotic notation in n; for small n the Fano bound is vacuous
--   - encoding: O(n^2/k) → ∃ C before n and k, for all n ≥ 1; reason: an absolute constant; n ≥ 1 only excludes the division 0/0
--   - encoding: learn |ψ⟩ ∈ Stab → for every stabilizer state ψ, with probability ≥ 2/3 the output v satisfies ‖v‖ = 1 and |⟨v, ψ⟩| = 1; reason: learning a state means recovering it up to a global phase; 2/3 is the paper's success convention (Theorem 6.6)
--   - encoding: uses k qubits of memory → memory of exactly k qubits (MemProtocol n k t X), t rounds = t copies; reason: the published model; unused memory qubits embed "at most k"
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Theorem 1.2, p. 5; §6.1 ("Putting the protocol together"), p. 55; Theorem 6.6, p. 56

import Definitions.Def_StabTestMem_Supplement_NALearner
import Definitions.Def_QAlgorithms_Defs_StabilizerLearning

namespace StabTestMem.Supplement

open QAlgorithms

/-- **Theorem 1.2 (optimal learning bounds), both halves; corrected range of the upper bound.**
Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*,
arXiv:2607.02444 (version of 2 Nov 2026), Theorem 1.2, p. 5: "Let k ≥ 1. There is a non-adaptive
protocol that uses k qubits of memory and O(n^2/k) copies of an unknown |ψ⟩ ∈ Stab to learn |ψ⟩.
Also, every non-adaptive protocol needs Ω(n^2/k) copies." (Proof: §6.1, "Putting the protocol
together", p. 55, and Theorem 6.6, p. 56.)

(Upper) There is an absolute constant `C` such that for all `n ≥ 1` and `k ≥ 1` some non-adaptive
learner (`StabTestMem.Supplement.NALearner`: precommitted randomness, then non-adaptive protocols
of the published `StabTestMem.MemProtocol` with exactly `k` memory qubits) using
`t ≤ C n² / min(k, n)` copies outputs, for every `n`-qubit stabilizer state `ψ` (the published
`QAlgorithms.IsStabilizerState`), a unit vector equal to `ψ` up to a global phase with probability
at least `2/3`.
(Lower) There are `c > 0` and `n₀` such that for every `n ≥ n₀`, every `k ≥ 1`, every finite
outcome alphabet and every non-adaptive learner with `k` memory qubits and `t` copies that learns
every stabilizer state with probability at least `2/3`, `t ≥ c n² / k`.

**Formalization Note.** Correction (upper): the printed `O(n²/k)` for every `k ≥ 1` is false for
`k` large (`n = 1`, `k > C`: `t ≤ C/k < 1` forces `t = 0`, and a `0`-copy learner's output law does
not depend on `ψ`, while the six one-qubit stabilizer states are pairwise distinct up to phase, so
some state is learned with probability `≤ 1/6`); the paper's proof (blocks of size `≤ k`,
`m = ⌈n/k⌉`, p. 53; "O(n) ≤ O(n²/k) for k ≤ n", p. 55) gives `O(n²/min(k, n))`, which is the
printed bound for `k ≤ n`. Reading: "non-adaptive" includes precommitted shared randomness
(random Clifford branches, pp. 52, 55). Reading (lower): `Ω` is asymptotic in `n` (`∃ n₀`).
`1 ≤ n` in the upper half only excludes the division `0/0`. "Learn |ψ⟩" is output `v` with
`‖v‖ = 1` and `|⟨v, ψ⟩| = 1`. -/
theorem optimal_learning_bounds :
    (∃ C : ℝ, ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      ∃ (X : Type) (_ : Fintype X) (t : ℕ)
        (L : NALearner n k t X (EuclideanSpace ℂ (Qubits n))),
        (t : ℝ) ≤ C * (n : ℝ) ^ 2 / ((min k n : ℕ) : ℝ) ∧
        ∀ ψ : EuclideanSpace ℂ (Qubits n), IsStabilizerState ψ →
          2 / 3 ≤ L.prob (ObliviousRSP.pureState ψ)
            (fun v => ‖v‖ = 1 ∧ ‖inner ℂ v ψ‖ = 1)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ k : ℕ, 1 ≤ k →
      ∀ (X : Type) [Fintype X] (t : ℕ)
        (L : NALearner n k t X (EuclideanSpace ℂ (Qubits n))),
        (∀ ψ : EuclideanSpace ℂ (Qubits n), IsStabilizerState ψ →
          2 / 3 ≤ L.prob (ObliviousRSP.pureState ψ)
            (fun v => ‖v‖ = 1 ∧ ‖inner ℂ v ψ‖ = 1)) →
        c * (n : ℝ) ^ 2 / (k : ℝ) ≤ t) := by sorry

end StabTestMem.Supplement
