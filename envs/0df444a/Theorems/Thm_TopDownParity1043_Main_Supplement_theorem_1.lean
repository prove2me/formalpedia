-- Prove2me | Theorems.Thm_TopDownParity1043_Main_Supplement_theorem_1
-- name    : TopDownParity1043.Main.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:52:35.942208+00:00
-- url     : https://prove2.me/theorems/9b8db702-b6e5-4f21-b9c4-f4233c37e3bf
-- title:
--   Theorem 1 — the initial parity lower bound $m > n^{3^{-d}}$ for all depths, with threshold $n\ge 64^{3^d}$
-- statement:
--   This is the paper's first, fully explicit lower bound for the Karchmer–Wigderson game of parity.
--
--   For a natural number $n$, $\mathrm{Parity}_n:\{0,1\}^n\to\{0,1\}$ is one exactly on the words of odd Hamming weight. In the game $\mathrm{KW}(\mathrm{Parity}_n)$, Alice holds an even-weight word $x$, Bob an odd-weight word $y$, and they must agree on a coordinate $i$ with $x_i\ne y_i$. A **$d$-round protocol of cost $m$** sends at most $d$ messages, each chosen by the player whose turn the transcript determines and taking at most $2^m$ values; every actual input pair must end at a leaf announcing a differing coordinate. The **wires** $W(C)$ of an AND/OR circuit $C$ are the total number of gate-input occurrences.
--
--   Let $n,d\in\mathbb N$ (no restriction on $d$) with
--   $$n\ \ge\ 64^{3^d}.$$
--   Then both of the following hold.
--
--   1. For every natural cost $m$ with $m\le n^{3^{-d}}$, $\mathrm{KW}(\mathrm{Parity}_n)$ has no $d$-round protocol of cost $m$.
--   2. Every AND/OR circuit $C$ of depth at most $d$ computing $\mathrm{Parity}_n$ has
--   $$W(C)\ >\ 2^{\,n^{3^{-d}}}.$$
--
--   The circuit clause depends only on the threshold on $n$, not on any cost $m$. This is the paper's initial top-down lower bound (Section 2), with explicit constants; the stronger Theorems 2 and 3 improve the exponent at the price of an unspecified constant and threshold.
--
--   **Formalization Note** The threshold is the natural-number power $64^{(3^d)}$, the exponent $3^{-d}$ is the real number $1/3^d$, and $n^{3^{-d}}$ is the real power. Protocols, KW solvability, parity and wires are the published definitions of the base mission.
--
--   Differences from the source:
--   - encoding: at most d messages of at most m bits, with a coordinate output → finite trees with at most 2^m children per node, height at most d and optional outputs; reason: the node fixes the transcript and speaker; every actual input pair must output a differing coordinate, and missing outputs only represent empty reached rectangles
--   - generalization: De Morgan circuits without an explicit constant and empty-gate convention → the referenced AND/OR DAGs also allow constants, empty gates and literal or constant outputs; reason: this includes every source circuit with the same depth and wire count; constants and empty gates can be simplified without increasing either resource
-- source:
--   Oliver Korten, STOC 2027 submission #1043 (October 2026), Theorem 1, p. 5

import Mathlib
import Definitions.Def_TopDownParity1043_Main_KW

set_option autoImplicit false

namespace TopDownParity1043.Main.Supplement

open TopDownParity1043.Main

/-- Theorem 1, p.5, both conclusions, for every natural depth `d` (including 0 and 1).
The threshold is the natural power `64 ^ (3 ^ d)`; the exponent `3^{-d}` is the real
number `1 / 3 ^ d`. The communication clause is for every cost `m ≤ n^{3^{-d}}`; the circuit
clause depends only on the threshold, and its wire bound is strict. -/
theorem theorem_1 (n d : ℕ) (hn : 64 ^ (3 ^ d) ≤ n) :
    (∀ m : ℕ, (m : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / (3 : ℝ) ^ d) →
      ¬ HasKWProtocol (parity n) d m) ∧
    (∀ C : ParityBarrier563.Trilinear.Circuit (Fin n),
      C.depth ≤ d → C.Computes (parity n) →
      (2 : ℝ) ^ ((n : ℝ) ^ ((1 : ℝ) / (3 : ℝ) ^ d)) < (wires C : ℝ)) := by sorry

end TopDownParity1043.Main.Supplement
