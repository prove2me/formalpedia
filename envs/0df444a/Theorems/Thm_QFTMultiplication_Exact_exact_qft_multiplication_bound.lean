-- Prove2me | Theorems.Thm_QFTMultiplication_Exact_exact_qft_multiplication_bound
-- name    : QFTMultiplication.Exact.exact_qft_multiplication_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:55:52.72847+00:00
-- url     : https://prove2.me/theorems/e2dd2fce-e533-4454-8706-97f30712cbff
-- title:
--   Theorem 1.1 — exact QFT at the multiplication gate bound
-- statement:
--   Fix any real $\alpha>0$ and a well-formed Boolean family computing the full product of two unsigned $n$-bit integers, with actual gate count $M(n)=O(n(\log_2 n)^\alpha)$. There are positive constants $C_g,C_a$, depending on $\alpha$ and this family but independent of $q$, such that for every integer $q\ge64$ there is an actual finite quantum circuit $c_q$ on $q+a_q$ wires with
--   $$
--   U_{c_q}(\psi\otimes|0^{a_q}\rangle)
--   =(F_q\psi)\otimes|0^{a_q}\rangle\quad\text{for every }\psi,
--   $$
--   $$
--   |c_q|\le C_gq(\log_2 q)^\alpha,\qquad
--   a_q\le C_aq(\log_2 q)^\alpha.
--   $$
--   The primitive gates are H, CNOT, every integer-numerator dyadic phase of Equation (3), and a single rotation type $B(\theta_q)$ whose angle is independent of the input. The transform is the normalized positive-sign cyclic QFT on $2^q$ labels, with the declared final bit order and literal global phase. All temporary qubits are counted and restored to zero.
--
--   This is the paper's full-strength exact headline result. It permits every fixed $\alpha>0$, including $\alpha<1$, and every integer $q\ge64$ without a power-of-two restriction on $q$. No uniform algorithm for generating the circuits or computing the extra angle is claimed.
--
--   **Formalization Note** A half-error inverse operator $V$ witnesses the source's angle through Equations (7)–(8). The constants are quantified before $q$; the assumed multiplication bound may have an eventual threshold.
--
--   Differences from the source:
--   - encoding: equality on all quantum states with clean auxiliaries → literal equality on all complex vectors with clean auxiliaries; reason: linearity makes these conditions equivalent, including preservation of global phase
--   - encoding: O-bounds → positive real gate and auxiliary constants before every register size; reason: this is the family-level asymptotic meaning, with allowable dependence only on the fixed data
--   - encoding: the size-dependent rotation from Equations (7)–(8) → a half-error inverse witness V and exactAngle q V; reason: the angle is constructed from size-dependent data, never an input state
-- source:
--   Chandrima Kayal, Rajat Mittal, Manaswi Paraashar, Nitin Saurabh, STOC 2027 submission #1075 (October 2026), Theorem 1.1 with gate-set continuation, pp. 3–4 (PDF pp. 3–4)

import Definitions.Def_QFTMultiplication_Exact_Model

set_option autoImplicit false

namespace QFTMultiplication.Exact

open QAlgorithms

/-- Theorem 1.1, pp.3–4. Fixed α>0 and the multiplication family precede the
positive constants; these precede every integer q≥64. V witnesses the source's
size-dependent angle (Equation (8)); it is independent of the input state. -/
theorem exact_qft_multiplication_bound (α : ℝ) (hα : 0 < α)
    (F : (n : ℕ) → BoolCircuit (n + n) (2 * n))
    (hF : MultCorrect F) (hM : MultBound α F) :
    ∃ Cg Ca : ℝ, 0 < Cg ∧ 0 < Ca ∧ ∀ q : ℕ, 64 ≤ q →
      ∃ (V : Op q), V ∈ Matrix.unitaryGroup (Qubits q) ℂ ∧
        specNorm (V - star (qftQubits q)) ≤ 1 / 2 ∧
        ∃ (a : ℕ) (c : Circuit (exactGates (exactAngle q V)) (q + a)),
          CleanImplements c (qftQubits q) ∧
          (c.size : ℝ) ≤ Cg * exactBudget α q ∧ (a : ℝ) ≤ Ca * exactBudget α q := by sorry

end QFTMultiplication.Exact
