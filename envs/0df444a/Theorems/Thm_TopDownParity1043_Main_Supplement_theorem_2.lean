-- Prove2me | Theorems.Thm_TopDownParity1043_Main_Supplement_theorem_2
-- name    : TopDownParity1043.Main.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:53:12.751567+00:00
-- url     : https://prove2.me/theorems/da68ea55-bff3-454b-9867-2bcafb13003e
-- title:
--   Theorem 2 — the improved parity lower bound with exponent $1/(2d-2)$ at every depth $d\ge2$
-- statement:
--   This is the paper's improved lower bound for the Karchmer–Wigderson game of parity, obtained from the strong mirror set lemma of Section 3.
--
--   $\mathrm{Parity}_n$ is one exactly on words of odd Hamming weight; in $\mathrm{KW}(\mathrm{Parity}_n)$ Alice holds an even-weight word, Bob an odd-weight word, and they must output a coordinate where the two differ. A $d$-round protocol of cost $m$ sends at most $d$ messages, each taking at most $2^m$ values, with the speaker determined by the transcript. The wires $W(C)$ of an AND/OR circuit are its gate-input occurrences.
--
--   For each natural depth $d\ge2$, there are a single constant $\varepsilon_d>0$ and a threshold $N_d\in\mathbb N$, both depending only on $d$, such that every $n\ge N_d$ satisfies both conclusions:
--
--   1. For every natural cost $m$,
--   $$m\le\varepsilon_d\, n^{1/(2d-2)}\quad\Longrightarrow\quad\mathrm{KW}(\mathrm{Parity}_n)\text{ has no }d\text{-round protocol of cost }m.$$
--   2. Every AND/OR circuit $C$ of depth at most $d$ computing $\mathrm{Parity}_n$ satisfies
--   $$W(C)\ >\ 2^{\varepsilon_d\, n^{1/(2d-2)}}.$$
--
--   The same $\varepsilon_d$ serves both clauses. The result is an intermediate step between the explicit Theorem 1 and the nearly tight Theorem 3 (exponent $1/(d-1)$).
--
--   **Formalization Note** The exponent $1/(2d-2)$ is computed in $\mathbb R$ after casting $d$, and powers are real powers. Protocols, KW solvability, parity and wires are the published definitions of the base mission.
--
--   Differences from the source:
--   - encoding: for each d there is ε_d > 0, provided n is sufficiently large → one positive ε and a natural threshold N chosen after d and before every n, m and circuit; reason: this expands sufficiently large with its correct dependence and uses real powers for 1/(2d-2)
--   - encoding: at most d messages of at most m bits, with a coordinate output → finite trees with at most 2^m children per node, height at most d and optional outputs; reason: the node fixes the transcript and speaker; every actual input pair must output a differing coordinate, and missing outputs only represent empty reached rectangles
--   - generalization: De Morgan circuits without an explicit constant and empty-gate convention → the referenced AND/OR DAGs also allow constants, empty gates and literal or constant outputs; reason: this includes every source circuit with the same depth and wire count; constants and empty gates can be simplified without increasing either resource
-- source:
--   Oliver Korten, STOC 2027 submission #1043 (October 2026), Theorem 2, p. 12

import Mathlib
import Definitions.Def_TopDownParity1043_Main_KW

set_option autoImplicit false

namespace TopDownParity1043.Main.Supplement

open TopDownParity1043.Main

/-- Theorem 2, p.12, both conclusions with one shared positive constant and one threshold
depending on `d` only. The real exponent is `1 / (2 * (d : ℝ) - 2)`, computed in `ℝ`.
The circuit bound counts wire occurrences and is strict. -/
theorem theorem_2 (d : ℕ) (hd : 2 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ m : ℕ, (m : ℝ) ≤ ε * (n : ℝ) ^ (1 / (2 * (d : ℝ) - 2)) →
        ¬ HasKWProtocol (parity n) d m) ∧
      (∀ C : ParityBarrier563.Trilinear.Circuit (Fin n),
        C.depth ≤ d → C.Computes (parity n) →
        (2 : ℝ) ^ (ε * (n : ℝ) ^ (1 / (2 * (d : ℝ) - 2))) < (wires C : ℝ)) := by sorry

end TopDownParity1043.Main.Supplement
