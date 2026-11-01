-- Prove2me | Theorems.Thm_ShendeQSD_Synthesis_muxRy_cz_count
-- name    : ShendeQSD.Synthesis.muxRy_cz_count
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:59.884778+00:00
-- url     : https://prove2.me/theorems/668b0be7-6fff-4ee8-ae13-3465852fab3c
-- title:
--   Appendix A.1: a multiplexed $R_y$ with $2^k$ controlled-Z gates, one initial (or terminal)
-- statement:
--   Let $k\ge1$ and let $\theta$ assign an angle $\theta_s$ to each $s\in\{0,1\}^k$. Consider the multiplexed $R_y$ gate on $k+1$ qubits with target the top wire and selects the $k$ wires below it.
--
--   1. Some circuit of one-qubit gates and controlled-Z gates implements it exactly, contains exactly $2^k$ controlled-Z gates, and its first gate is a controlled-Z.
--   2. Some such circuit, with exactly $2^k$ controlled-Z gates, has a controlled-Z as its last gate.
--
--   Because a controlled-Z is diagonal, the initial (or terminal) one can be absorbed into the neighbouring generic multiplexor, which saves one two-qubit gate at every step of the recursion; this is the first of the two optimizations leading to Eq. (19).
--
--   **Formalization Note** The first gate of a circuit is the head of its list of gates (the first applied). $R_y$ is the paper's.
--
--   Differences from the source:
--   - reading: "2^n controlled-Z gates" for the central multiplexed R_y of an n-qubit CSD → 2^k controlled-Z gates for a multiplexed R_y with k select qubits; reason: that gate has n − 1 selects, and Theorem 8 with Figure 2 gives 2^k for k selects; this is the stronger reading
--   - reading: "of which one is initial (or terminal)" → both: a circuit whose first gate is a controlled-Z and a circuit whose last gate is a controlled-Z; reason: the reversal remark after Theorem 8 (p. 11) gives both, and both are used
--   - reading: k select qubits → 1 ≤ k; reason: the multiplexed R_y of the CSD on n ≥ 2 qubits has at least one select
--   - encoding: the target drawn at the bottom in Theorem 8 → the target is wire 0, the selects are wires 1, …, k; reason: the same operator up to the order of the wires; it is the orientation of the CSD's central gate
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, Appendix A.1, pp. 16–17

import Definitions.Def_ShendeQSD_Synthesis_czLib
import Definitions.Def_ShendeQSD_Synthesis_muxRot
import Definitions.Def_ShendeQSD_Synthesis_ry

namespace ShendeQSD.Synthesis

open QAlgorithms

/-- **Appendix A.1: a multiplexed `R_y` with `2^k` controlled-Z gates, one of them initial (or
terminal).**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
Appendix A.1, pp. 16–17: "The statements and proofs of Theorem 8 and Figure 2 still hold for
multiplexed R_y gates if all CNOTs are replaced with controlled-Z gates. Thus the central
multiplexed R_y in the Cosine-Sine decomposition may be implemented with 2^n controlled-Z gates,
of which one is initial (or terminal)."

For every `k ≥ 1` and all angles `θ : {0,1}^k → ℝ`:
1. some circuit of one-qubit gates and controlled-Z gates on `k + 1` qubits implements the
   multiplexed `R_y` `muxRotQ ry θ` exactly, contains exactly `2^k` controlled-Z gates, and its
   first gate is a controlled-Z;
2. the same with the last gate a controlled-Z.

**Formalization Note.** Readings: the gate count is `2^k` for `k` select qubits (the central
multiplexed `R_y` of an `n`-qubit CSD has `k = n − 1` selects, and Theorem 8 with Figure 2 gives
`2^k`); "initial (or terminal)" is read as both: a circuit with a controlled-Z first and one with
a controlled-Z last. The first gate of a circuit is the head of the list (applied first).
Encoding: the target is wire `0`, the selects are wires `1, …, k`. -/
theorem muxRy_cz_count (k : ℕ) (hk : 1 ≤ k) (θ : Qubits k → ℝ) :
    (∃ c : Circuit czLib (k + 1), c.unitary = muxRotQ ry θ ∧ czCount c = 2 ^ k ∧
      ∃ g ∈ c.head?, g.gate.arity = 2) ∧
    (∃ c : Circuit czLib (k + 1), c.unitary = muxRotQ ry θ ∧ czCount c = 2 ^ k ∧
      ∃ g ∈ c.getLast?, g.gate.arity = 2) := by sorry

end ShendeQSD.Synthesis
