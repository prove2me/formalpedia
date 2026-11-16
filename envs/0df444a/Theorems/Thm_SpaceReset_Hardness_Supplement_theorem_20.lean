-- Prove2me | Theorems.Thm_SpaceReset_Hardness_Supplement_theorem_20
-- name    : SpaceReset.Hardness.Supplement.theorem_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:42:00.374649+00:00
-- url     : https://prove2.me/theorems/855dc5c5-65ec-41c6-8441-8d974aee1979
-- title:
--   Theorem 20 — online parity measurement frontier
-- statement:
--   Let $m\ge1$ and $0\le\varepsilon<1/4$, and consider the parity schedule $\mathcal P_m$: $2m$ disjoint parity checks over $4m$ slots. The first $m$ pairs arrive consecutively; then all first members of the last $m$ pairs arrive before their second members. Each data qubit is returned in its arrival slot, and the syndrome accompanies the second member.
--
--   An implementation has $q$ persistent private qubits, which count every retained record, and a freely chosen initializer. Fresh registers are pure, and the discarded Stinespring environments have product dimension at most $2^g$. Such an implementation with operational error at most $\varepsilon$ against adaptive input/reference testers exists if and only if
--   $$q\ge m,\qquad q+g\ge m+\lceil m/2\rceil .$$
--   Moreover, every feasible pair $(q,g)$ admits an exact Clifford implementation with the following properties:
--
--   1. it uses $q+2$ device qubits, namely the $q$ private cells and the current data and syndrome carriers;
--   2. exactly $\lfloor m/2\rfloor$ cells start maximally mixed and all other cells start pure;
--   3. its only gates are Clifford gates and single-qubit RESETs, at most $g$ of them;
--   4. the syndrome carrier is used only on the slots where a syndrome is returned.
--
--   Exact peak optimality is not asserted.
--
--   This frontier separates the instrument from its ordered Choi state; Corollary 3 then specializes it to a fixed initializer.
--
--   Differences from the source:
--   - encoding: the arrival order of P_m (1-based slots, Figure 1) → 0-based slots: check c < m at 2c, 2c + 1; check m + i at 2m + i and 3m + i; reason: the same order
--   - encoding: the instrument M on each check, coherent within parity sectors → an online process with one accumulator bit per check (never returned) that adds both data bits and is copied to the syndrome output; reason: tracing out the accumulator dephases the syndrome exactly as M does and changes nothing else
--   - encoding: data output alone on slots without a syndrome → the output register is Bool × (SynIdx m j → Bool), whose second factor is one-dimensional when no check closes at slot j; reason: a one-dimensional factor carries no information
--   - encoding: operational error = trace distance maximized over adaptive input/reference testers → for every valid adaptive tester and every slot j < N, the trace distance of the tester states right after slot j is at most ε; reason: a tester can carry any earlier state to the end in its reference and a final channel only contracts trace distance, so this equals the bound on the final state
--   - encoding: ⌈m/2⌉ and ⌊m/2⌋ → (m + 1) / 2 and m / 2 in ℕ; reason: equal for every natural m
--   - reading: exact Clifford implementation with single-qubit resets only for the feasible pair (q, g) → a ParityCircuit using H, S, controlled-X/Y/Z and RESET only (no D_Z), with at most g RESETs and error 0; reason: an implementation within budget g discards at most g qubits, one per RESET
--   - encoding: device peak at most q + 2 including current data and syndrome carriers → a circuit on q + 2 wires whose syndrome wire is untouched on slots without a syndrome (SynClean); reason: there the syndrome carrier does not exist in the source; it stays a fresh |0⟩ and discards nothing
-- source:
--   Rinka Miura, STOC 2027 submission #1715 (October 2026), The Complexity of Space–Reset Tradeoffs in Online Quantum Computation (held submission, no arXiv version; SHA-256 c2a340e2195da0d130bf10d936d56d4f1d4da805e644efb7fe1c36d9c904f3e5), Theorem 20, pp. 29–30 (setting p. 29; schedule p. 8 and Figure 1, p. 9; construction §4.2, p. 31)

import Mathlib
import Definitions.Def_SpaceReset_Hardness_Supplement_Online

set_option autoImplicit false

namespace SpaceReset.Hardness.Supplement

open SpaceReset.Hardness

/-- Theorem 20 (Online parity measurement frontier), §4, pp. 29–30.

For `m ≥ 1` and `0 ≤ ε < 1/4`, the parity schedule `P_m` (`4m` slots) has an implementation with
`q` persistent private qubits, discarded capacity `g` qubits and any initializer, at operational
error at most `ε`, if and only if `q ≥ m` and `q + g ≥ m + ⌈m/2⌉`. Every feasible pair admits an
exact Clifford implementation on `q + 2` device qubits (the `q` private cells plus the current data
and syndrome carriers) with exactly `⌊m/2⌋` initially maximally mixed cells, all other cells pure,
no gates other than Clifford gates and single-qubit `RESET`s, and at most `g` `RESET`s. -/
theorem theorem_20 :
    (∀ m : ℕ, 1 ≤ m → ∀ ε : ℝ, 0 ≤ ε → ε < 1 / 4 → ∀ q g : ℕ,
      (∃ D : ODevice PmIn (PmOut m) (4 * m) q g,
          OErrorLE (4 * m) D.toProcess (parityTarget m) ε) ↔
        (m ≤ q ∧ m + (m + 1) / 2 ≤ q + g)) ∧
    ∀ m : ℕ, 1 ≤ m → ∀ q g : ℕ, m ≤ q → m + (m + 1) / 2 ≤ q + g →
      ∃ C : ParityCircuit m q, C.CliffordResetOnly ∧ C.SynClean ∧ C.mixedCount = m / 2 ∧
        C.resetCount ≤ g ∧ OErrorLE (4 * m) C.toProcess (parityTarget m) 0 := by sorry

end SpaceReset.Hardness.Supplement
