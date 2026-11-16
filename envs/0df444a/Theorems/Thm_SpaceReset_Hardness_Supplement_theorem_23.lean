-- Prove2me | Theorems.Thm_SpaceReset_Hardness_Supplement_theorem_23
-- name    : SpaceReset.Hardness.Supplement.theorem_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:43:11.1198+00:00
-- url     : https://prove2.me/theorems/b198b34e-750e-49c9-8143-3ef9be3c11b4
-- title:
--   Theorem 23 — every ordered cut can agree while the costs differ
-- statement:
--   For every integer $a\ge1$ there are two repeated-bit sources $G_A,G_B$ on $n=4a+4$ output qubits, each of rank $k=2a+2$ and taken in their given output order, with the following properties.
--
--   1. For every cut $t\in\{0,\dots,n\}$, their emitted code states $\rho_{C_A},\rho_{C_B}$ are related by a Clifford unitary on the first $t$ qubits tensored with a Clifford unitary on the remaining $n-t$ qubits.
--   2. Their invariants are
--   $$c_A=c_B=a+1,\qquad \Pi_A=3a+2,\qquad \Pi_B=2a+2 .$$
--   3. For every error $0\le\varepsilon\le1/64$ and both output contracts (joint code-state generation and the full adaptive phase process), the least closed memories are
--   $$Q_A=\Big\lceil\tfrac{3a+2}{2}\Big\rceil,\qquad Q_B=a+1,\qquad Q_A-Q_B=\lceil a/2\rceil .$$
--   Here closed means a Definition 4 device with no discarded environment ($g=0$) and any, possibly mixed, initializer.
--   4. At the common minimum retained memory $q=a+1$, the least discarded capacities are $g_A=a$ and $g_B=0$.
--
--   The theorem shows that the information present at every single cut does not determine the online resource cost.
--
--   Differences from the source:
--   - encoding: two repeated-bit sources (each symbol one independent fair bit occurring exactly twice) → G_A, G_B : Matrix (Fin (2a+2)) (Fin (4a+4)) F2 satisfying IsRepeatedBitSource (full row rank, unit columns, row weight two); reason: the source definition of p. 36
--   - encoding: entire bipartite output density operators → the base emitted code states codeState G_A, codeState G_B; reason: the joint output state of a binary source
--   - encoding: Clifford unitary → a product of the gate matrices of H, S and controlled-X/Y/Z; reason: these generate the Clifford group up to a global phase, which cancels under conjugation
--   - encoding: optimal sizes Q_A, Q_B, g_A, g_B → IsLeast of the sets of feasible q (with g = 0) and of feasible g (with q = a + 1) over Definition 4 devices; reason: attained least values
--   - encoding: ⌈(3a+2)/2⌉ and ⌈a/2⌉ → (3a + 3) / 2 and (a + 1) / 2 in ℕ, with Q_A − Q_B in ℕ; reason: equal for every natural a, and Q_A ≥ Q_B
-- source:
--   Rinka Miura, STOC 2027 submission #1715 (October 2026), The Complexity of Space–Reset Tradeoffs in Online Quantum Computation (held submission, no arXiv version; SHA-256 c2a340e2195da0d130bf10d936d56d4f1d4da805e644efb7fe1c36d9c904f3e5), Theorem 23, p. 36 (proof pp. 36–37)

import Mathlib
import Definitions.Def_SpaceReset_Hardness_DiscardDevice
import Definitions.Def_SpaceReset_Hardness_Supplement_Sources

set_option autoImplicit false

namespace SpaceReset.Hardness.Supplement

open SpaceReset.Hardness

/-- Theorem 23 (Every ordered cut can agree while the costs differ), App. A, p. 36.

For every integer `a ≥ 1` there are two repeated-bit sources `G_A`, `G_B` on `n = 4a + 4` output
qubits, each of rank `k = 2a + 2`, in their given output order, such that at every cut
`t ∈ {0,…,n}` their emitted code states are related by a Clifford unitary on the first `t` qubits
tensored with a Clifford unitary on the last `n − t` qubits; `c_A = c_B = a + 1`,
`Π_A = 3a + 2`, `Π_B = 2a + 2`; and for every error `0 ≤ ε ≤ 1/64` and both output contracts the
least closed memory (Definition 4 devices with `g = 0`, any initializer) is
`Q_A = ⌈(3a+2)/2⌉` and `Q_B = a + 1`, with `Q_A − Q_B = ⌈a/2⌉`, and at memory `q = a + 1` the
least discarded capacity is `g_A = a` and `g_B = 0`. -/
theorem theorem_23 :
    ∀ a : ℕ, 1 ≤ a →
      ∃ GA GB : Matrix (Fin (2 * a + 2)) (Fin (4 * a + 4)) F2,
        IsRepeatedBitSource GA ∧ IsRepeatedBitSource GB ∧
        (∀ t : ℕ, t ≤ 4 * a + 4 → LocallyCliffordEquiv t (codeState GA) (codeState GB)) ∧
        cInv GA = a + 1 ∧ cInv GB = a + 1 ∧ PiInv GA = 3 * a + 2 ∧ PiInv GB = 2 * a + 2 ∧
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 64 → ∀ c : Contract,
          IsLeast {q : ℕ | ∃ D : DiscardDevice (4 * a + 4) q 0, ErrorLE GA c D.toProcess ε}
            ((3 * a + 3) / 2) ∧
          IsLeast {q : ℕ | ∃ D : DiscardDevice (4 * a + 4) q 0, ErrorLE GB c D.toProcess ε}
            (a + 1) ∧
          (3 * a + 3) / 2 - (a + 1) = (a + 1) / 2 ∧
          IsLeast {g : ℕ | ∃ D : DiscardDevice (4 * a + 4) (a + 1) g, ErrorLE GA c D.toProcess ε}
            a ∧
          IsLeast {g : ℕ | ∃ D : DiscardDevice (4 * a + 4) (a + 1) g, ErrorLE GB c D.toProcess ε}
            0 := by sorry

end SpaceReset.Hardness.Supplement
