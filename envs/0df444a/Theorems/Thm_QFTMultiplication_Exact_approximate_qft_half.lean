-- Prove2me | Theorems.Thm_QFTMultiplication_Exact_approximate_qft_half
-- name    : QFTMultiplication.Exact.approximate_qft_half
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:55:42.692385+00:00
-- url     : https://prove2.me/theorems/f7ae700e-cd10-43ab-8a6f-437af352e8d7
-- title:
--   Theorem 2.5 — constant-error approximate QFT
-- statement:
--   Fix a real $\alpha>0$ and a full integer-multiplication family with $M(n)=O(n(\log_2 n)^\alpha)$. There are positive constants $C_g,C_a$, depending on these fixed data, such that every integer $q\ge64$ has a unitary $W$ and clean physical circuits for $W$ and $W^\dagger$ satisfying
--   $$
--   \|W-F_q\|_{\mathrm{op}}\le\tfrac12,\qquad
--   \|W^\dagger-F_q^\dagger\|_{\mathrm{op}}\le\tfrac12,
--   $$
--   $$
--   |c|,|c^{-}|\le C_gq(\log_2\log_2 q)^{\alpha+1},\qquad
--   a\le C_aq(\log_2\log_2 q)^{\alpha+1}.
--   $$
--   Both circuits use only H, CNOT, and Equation (3) phases, have the same gate count and the same auxiliary register size, and return every auxiliary qubit to zero. This gives the constant-error input required for exactification.
--
--   **Formalization Note** The effective operator $W$ acts on $q$ qubits; its physical implementations act on $q+a$ qubits. The spectral norm is the Euclidean operator norm, without minimization over global phases.
--
--   Differences from the source:
--   - encoding: equality on all quantum states with clean auxiliaries → literal equality on all complex vectors with clean auxiliaries; reason: linearity makes these conditions equivalent, including preservation of global phase
--   - encoding: O-bounds → positive real gate and auxiliary constants before every register size; reason: this is the family-level asymptotic meaning, with allowable dependence only on the fixed data
--   - encoding: the inverse circuit has the same resources → an explicit inverse-operator implementation with equal list length and the same auxiliary size; reason: reversal of the basic-gate list realizes these resource clauses
-- source:
--   Chandrima Kayal, Rajat Mittal, Manaswi Paraashar, Nitin Saurabh, STOC 2027 submission #1075 (October 2026), Theorem 2.5, p. 8 (PDF p. 8)

import Definitions.Def_QFTMultiplication_Exact_Model

set_option autoImplicit false

namespace QFTMultiplication.Exact

open QAlgorithms

/-- Theorem 2.5, p.8. Effective W and its adjoint have separate clean physical circuits.
Reversing a base-gate circuit preserves both its length and its workspace. -/
theorem approximate_qft_half (α : ℝ) (hα : 0 < α)
    (F : (n : ℕ) → BoolCircuit (n + n) (2 * n))
    (hF : MultCorrect F) (hM : MultBound α F) :
    ∃ Cg Ca : ℝ, 0 < Cg ∧ 0 < Ca ∧ ∀ q : ℕ, 64 ≤ q →
      ∃ (W : Op q) (a : ℕ) (c ci : Circuit baseGates (q + a)),
        W ∈ Matrix.unitaryGroup (Qubits q) ℂ ∧
        specNorm (W - qftQubits q) ≤ 1 / 2 ∧
        specNorm (star W - star (qftQubits q)) ≤ 1 / 2 ∧
        CleanImplements c W ∧ CleanImplements ci (star W) ∧ ci.size = c.size ∧
        (c.size : ℝ) ≤ Cg * halfBudget α q ∧ (a : ℝ) ≤ Ca * halfBudget α q := by sorry

end QFTMultiplication.Exact
