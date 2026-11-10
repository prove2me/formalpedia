-- Prove2me | Theorems.Thm_TopDownParity1043_Main_theorem_3
-- name    : TopDownParity1043.Main.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:20:04.426865+00:00
-- url     : https://prove2.me/theorems/987ec7f7-19b4-4dab-9b76-811c560374c6
-- title:
--   Theorem 3 — nearly tight parity lower bounds at every depth
-- statement:
--   For each natural depth $d\ge2$, there are a single constant $\varepsilon_d>0$ and a threshold $N_d\in\mathbb N$, both depending only on $d$, such that every $n\ge N_d$ satisfies both conclusions:
--
--   1. For every natural message cost $m$,
--   $$m\le\varepsilon_d n^{1/(d-1)}\quad\Longrightarrow\quad\mathrm{KW}(\mathrm{Parity}_n)\text{ has no at-most-}d\text{-round protocol of cost at most }m.$$
--   2. Every AND/OR circuit $C$ of depth at most $d$ computing parity satisfies the strict wire bound
--   $$W(C)>2^{\varepsilon_d n^{1/(d-1)}}.$$
--
--   Parity is one on words of odd Hamming weight. Protocols solve the coordinate search problem and may choose the speaker from the transcript. Wires count all gate-input occurrences in the referenced DAG model. The shared constant is quantified before $n$, the protocol and the circuit. This is the paper's final theorem; its numerical lower-bound form is classical, while the paper supplies a top-down proof.
--
--   Differences from the source:
--   - encoding: for each d there is ε_d > 0, provided n is sufficiently large → one positive ε and a natural threshold N chosen after d and before every n, m and circuit; reason: this expands sufficiently large with its correct dependence and uses real powers for 1/(d-1)
--   - encoding: at most d messages of at most m bits, with a coordinate output → finite trees with at most 2^m children per node, height at most d and optional outputs; reason: the node fixes the transcript and speaker; every actual input pair must output a differing coordinate, and missing outputs only represent empty reached rectangles
--   - generalization: De Morgan circuits without an explicit constant and empty-gate convention → the referenced AND/OR DAGs also allow constants, empty gates and literal or constant outputs; reason: this includes every source circuit with the same depth and wire count; constants and empty gates can be simplified without increasing either resource
-- source:
--   Oliver Korten, STOC 2027 submission #1043 (October 2026), Theorem 3, p. 15

import Mathlib
import Definitions.Def_TopDownParity1043_Main_KW

set_option autoImplicit false
open scoped NNReal ENNReal

namespace TopDownParity1043.Main

/-- Theorem 3, p.15, both conclusions with one shared positive constant and
one threshold depending on d only. The real exponent is 1 / ((d : ℝ) - 1).
The circuit bound counts wire occurrences and is strict. -/
theorem theorem_3 (d : ℕ) (hd : 2 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ m : ℕ, (m : ℝ) ≤ ε * (n : ℝ) ^ (1 / ((d : ℝ) - 1)) →
        ¬ HasKWProtocol (parity n) d m) ∧
      (∀ C : ParityBarrier563.Trilinear.Circuit (Fin n),
        C.depth ≤ d → C.Computes (parity n) →
        (2 : ℝ) ^ (ε * (n : ℝ) ^ (1 / ((d : ℝ) - 1))) < (wires C : ℝ)) := by sorry

end TopDownParity1043.Main
