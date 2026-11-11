-- Prove2me | Theorems.Thm_TightPQRepetition_Main_theorem_3_9
-- name    : TightPQRepetition.Main.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T23:34:26.467988+00:00
-- url     : https://prove2.me/theorems/f9f8befe-a67f-4fc9-b735-e086a465f453
-- title:
--   Theorem 3.9 — efficient clean-ancilla rotation (corrected: finite-dimensional $\mathcal H$)
-- statement:
--   There is a constant $c$ such that for all $\varepsilon,\delta\in(0,1)$ there is a circuit $C_{\varepsilon,\delta}$ with one ancilla qubit, $m$ calls to $C_{\Pi_B}NOT$, $m$ calls to $C_{\Pi_A}NOT$ and $m$ single-qubit gates on the ancilla, $m=O(\log(1/\varepsilon)/\delta)$, such that for all Hermitian projectors $\Pi_A,\Pi_B$ on a finite-dimensional space:
--
--   1. for every state $|\psi\rangle$, $C_{\varepsilon,\delta}^{\Pi_B,\Pi_A}(|\psi\rangle\otimes|0\rangle)=(U_{\varepsilon,\delta}^{\Pi_B,\Pi_A}|\psi\rangle)\otimes|0\rangle$ for a unitary $U_{\varepsilon,\delta}^{\Pi_B,\Pi_A}$;
--
--   2. for every singular value decomposition $\Pi_B\Pi_A=\sum_j\varsigma_j|w_j\rangle\langle v_j|$,
--   $$\Pi_BU_{\varepsilon,\delta}^{\Pi_B,\Pi_A}\Pi_A=\sum_j\tilde\varsigma_j|w_j\rangle\langle v_j|,$$
--   with $\tilde\varsigma_j$ real, in $[1-\varepsilon,1]$ if $\varsigma_j\ge\delta$, and in $[-1,1]$ otherwise.
--
--   This rotation plays the role of rewinding: it moves a state from the image of $\Pi_A$ back into the image of $\Pi_B$ while the ancilla stays exactly clean.
--
--   Differences from the source:
--   - correction: a Hilbert space → every finite-dimensional complex inner product space, of any dimension; reason: the sum over j does not exist in general in infinite dimensions; see Lemma 3.8; every use is on finitely many qubits
--   - generalization: for given projectors, there is a circuit → one circuit, depending only on ε and δ, for all projectors and dimensions; reason: the circuit of QSVT depends only on the polynomial, and Lemma 5.4 needs one oracle circuit for b = 0, 1; this implies the printed statement
--   - reading: m = O(log(1/ε)/δ) → m ≤ c · log(1/ε)/δ for one constant c, all ε, δ ∈ (0,1), all projectors and all dimensions; reason: the O(·) with its constant made explicit and uniform, as Lemmas 5.4 and 5.6 need
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Theorem 3.9, printed p. 13 / PDF p. 15

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Jordan

namespace TightPQRepetition.Main

/-- Theorem 3.9 (printed p. 13, PDF p. 15). -/
theorem theorem_3_9 : ∃ (c : ℝ) (prog : ℝ → ℝ → RotationProgram), 0 < c ∧
    IsRotationFamily c prog := by sorry

end TightPQRepetition.Main
