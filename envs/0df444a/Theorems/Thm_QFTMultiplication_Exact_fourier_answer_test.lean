-- Prove2me | Theorems.Thm_QFTMultiplication_Exact_fourier_answer_test
-- name    : QFTMultiplication.Exact.fourier_answer_test
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:55:45.927864+00:00
-- url     : https://prove2.me/theorems/56804ce0-7d21-4a77-99b0-4593944bff20
-- title:
--   Lemma 2.3 — Fourier-state answer test
-- statement:
--   Fix a full integer-multiplication family and its gate count $M(q)$. For every nonnegative integer $q$ there is a unitary $D$ on $q$-qubit registers $I,O$ and one flag qubit $E$ with
--   $$
--   D(|\phi_x\rangle_I|y\rangle_O|b\rangle_E)
--   =(-1)^{\mathbf1\{x=y,\ b=1\}}|\phi_x\rangle_I|y\rangle_O|b\rangle_E
--   $$
--   for all $0\le x,y<2^q$ and both $b\in\{0,1\}$. It has a clean physical implementation using only H, CNOT, and Equation (3) phases, with $O(M(q))$ gates and temporary qubits. In particular there are constants $C_g,C_a>0$ independent of $q$ with $|c|\le C_gM(q)$ and $a\le C_aM(q)$ for every $q\ge1$; a clean implementation also exists at $q=0$.
--
--   All temporary qubits return to zero. The input, output-label, and flag registers are designated registers. This unitary supplies the phase test on the correct-answer subspace.
--
--   Differences from the source:
--   - encoding: equality on all quantum states with clean auxiliaries → literal equality on all complex vectors with clean auxiliaries; reason: linearity makes these conditions equivalent, including preservation of global phase
--   - encoding: O-bounds → positive real gate and auxiliary constants before every register size; reason: this is the family-level asymptotic meaning, with allowable dependence only on the fixed data
--   - encoding: O(M(q)) and no lower size restriction on the operation → existence at every q, with the global resource inequalities for q≥1; reason: an asymptotic bound imposes no cost inequality at q=0, where M(0) may be zero and D is Z on the flag
-- source:
--   Chandrima Kayal, Rajat Mittal, Manaswi Paraashar, Nitin Saurabh, STOC 2027 submission #1075 (October 2026), Lemma 2.3, p. 7 (PDF p. 7)

import Definitions.Def_QFTMultiplication_Exact_Model

set_option autoImplicit false

namespace QFTMultiplication.Exact

open QAlgorithms

/-- Lemma 2.3, p.7. Every q, including zero, has the specified unitary.
The O(M(q)) inequality is global for positive q; no constraint at q=0 is part of an
asymptotic bound (M(0) may be zero, whereas this test can use a Z gate). -/
theorem fourier_answer_test
    (F : (n : ℕ) → BoolCircuit (n + n) (2 * n)) (hF : MultCorrect F) :
    ∃ Cg Ca : ℝ, 0 < Cg ∧ 0 < Ca ∧ ∀ q : ℕ,
      ∃ (D : Op ((q + q) + 1)) (a : ℕ)
        (c : Circuit baseGates (((q + q) + 1) + a)),
        D ∈ Matrix.unitaryGroup (Qubits ((q + q) + 1)) ℂ ∧
        (∀ (x y : Qubits q) (b : Bool),
          act D (answerInput q x y b) = answerSign x y b • answerInput q x y b) ∧
        CleanImplements c D ∧
        (1 ≤ q → (c.size : ℝ) ≤ Cg * multSize F q ∧ (a : ℝ) ≤ Ca * multSize F q) := by sorry

end QFTMultiplication.Exact
