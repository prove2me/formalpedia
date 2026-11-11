-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_lemma_3_6
-- name    : PSPACEOracleSynth.Main.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:31.147643+00:00
-- url     : https://prove2.me/theorems/79c05818-d71a-4d33-8145-e4f080db3158
-- title:
--   Lemma 3.6 — a parameterized circuit for a row-sparse near-isometry with error $5\varepsilon$
-- statement:
--   Let $\Lambda$ be a matrix with columns indexed by $v<d$, where $d\le2^n$, and rows indexed by $u<2^w$. Suppose that $\Lambda$ is an $\varepsilon$-near-isometry with $0\le\varepsilon<1$ and has a sparsity pattern of at most $N$ positions per row. Consider an index register of $n$ qubits, a row register of $w$ qubits and two flag qubits, with
--   $$\iota_{\mathrm{in}}|v\rangle=|v\rangle|0^w\rangle|0\rangle|0\rangle,\qquad\iota_{\mathrm{out}}|u\rangle=|0^n\rangle|u\rangle|1\rangle|1\rangle.$$
--   There is a parameterized circuit $C_\Lambda$ on these registers such that
--   $$\|C_\Lambda\iota_{\mathrm{in}}-\iota_{\mathrm{out}}\Lambda\|\le5\varepsilon.$$
--   It has $O(N(n+w))$ uniformly controlled gates, its gate list depends only on $n,w,N$, and its parameters are determined by $\Lambda$ and the pattern.
--
--   The lemma implements the two maps of each stage of the recursion coherently, with an error proportional to how far they are from isometries.
--
--   **Formalization Note.** The constant $c$ of the $O(\cdot)$ and the gate lists `skel n w N` are chosen before $\Lambda$; the parameters are one function `par` of $(n,w,N,d)$, $\Lambda$ and the pattern, not of $\varepsilon$. The circuit has exactly the $n+w+2$ wires of the three registers (index, row, flags, in this order); a register holding the integer $v$ carries bit $q$ of $v$ on its $q$-th wire.
--
--   Differences from the source:
--   - reading: O(N(n + w)) uniformly controlled gates → at most c·N·(n + w + 1) for one constant c chosen before n, w, N; reason: agrees with c'·N·(n + w) up to a factor 2 when n + w ≥ 1; at n = w = 0 the literal bound 0 is false (a fixed gate list over G cannot produce every phase of a 1×1 Λ)
--   - reading: its parameters are determined by Λ and the pattern, as given in Equations (3.10) and (3.11) → the parameters are par (n, w, N, d) Λ P for one function par chosen before Λ, P, ε; reason: Equations (3.10)–(3.11) are formulas of the proof for gates the statement does not name; the statement's content is that the parameters are a function of Λ and the pattern
--   - encoding: basis state |v⟩ of an n-qubit register for an integer v → bit q of v (Nat.testBit) on the q-th wire of the register; reason: a fixed relabelling of the basis; the lemma quantifies over all Λ and patterns
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), §3.4, Lemma 3.6, p. 21 (parameters: Equations (3.10)–(3.11), p. 22)

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Dilation
import Definitions.Def_PSPACEOracleSynth_Main_ParamCircuit

open QAlgorithms.Complexity

namespace PSPACEOracleSynth.Main

/-- **Lemma 3.6**, Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*, STOC 2027 submission
#1740, p. 21 (parameters, Equations (3.10)–(3.11), p. 22). Let `Λ` be a matrix with columns
indexed by `v < d`, `d ≤ 2^n`, and rows indexed by `u < 2^w`, which is an `ε`-near-isometry with
`0 ≤ ε < 1` and has a sparsity pattern of at most `N` positions per row. On an index register of
`n` qubits, a row register of `w` qubits and two flag qubits, with
`ι_in|v⟩ = |v⟩|0^w⟩|0⟩|0⟩` and `ι_out|u⟩ = |0^n⟩|u⟩|1⟩|1⟩`, there is a parameterized circuit
`C_Λ` with `‖C_Λ ι_in − ι_out Λ‖ ≤ 5ε`. It has `O(N(n + w))` uniformly controlled gates, its gate
list depends only on `n, w, N`, and its parameters are determined by `Λ` and the pattern.

The constant `c` of the `O(·)` and the gate lists `skel n w N` are chosen before `Λ`; the
parameters are one function `par` of the sizes, `Λ` and the pattern (not of `ε`). -/
theorem lemma_3_6 :
    ∃ (c : ℕ) (skel : (n w N : ℕ) → PCirc (n + w + 2)),
      (∀ n w N : ℕ, (skel n w N).ucCount ≤ c * N * (n + w + 1)) ∧
      ∃ par : (n w N d : ℕ) → Matrix (Fin (2 ^ w)) (Fin d) ℂ →
          (Fin (2 ^ w) → Finset (Fin d)) → PParams,
        ∀ (n w N d : ℕ) (Λ : Matrix (Fin (2 ^ w)) (Fin d) ℂ) (P : Fin (2 ^ w) → Finset (Fin d))
          (ε : ℝ), d ≤ 2 ^ n → 0 ≤ ε → ε < 1 → IsNearIsometry ε Λ → IsSparsityPattern Λ P →
          (∀ u, (P u).card ≤ N) →
          opNormR ((skel n w N).unitary (par n w N d Λ P) * iotaIn n w d - iotaOut n w * Λ)
            ≤ 5 * ε := by sorry

end PSPACEOracleSynth.Main
