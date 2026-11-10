-- Prove2me | Theorems.Thm_QFTMultiplication_Exact_one_grover_iterate
-- name    : QFTMultiplication.Exact.one_grover_iterate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:55:43.609345+00:00
-- url     : https://prove2.me/theorems/526e63e9-3ae2-49c7-82a6-e4c8aaf1163a
-- title:
--   Lemma 2.4 — one Grover iterate
-- statement:
--   There are absolute positive constants $C_g,C_a$ such that the reflection $R_0=2|0^m\rangle\langle0^m|-I$ on every $m$-qubit register has a clean H/CNOT/dyadic-phase implementation with at most $C_gm$ gates and $C_am$ temporary qubits.
--
--   Let $U,D$ be unitaries on that register, and let $|g\rangle,|h\rangle$ be orthogonal unit vectors with
--   $$
--   U|0^m\rangle=|s\rangle=\tfrac12|g\rangle+\tfrac{\sqrt3}{2}|h\rangle,
--   \qquad D|g\rangle=-|g\rangle,\quad D|h\rangle=|h\rangle.
--   $$
--   Then the four-call word, in temporal order $D,U^\dagger,R_0,U$, satisfies
--   $$
--   UR_0U^\dagger D|s\rangle=|g\rangle.
--   $$
--   Each of its four calls occurs once. Every temporary qubit for the reflection returns to zero. The statement makes no linear gate bound for the arbitrary unitaries $U,D$. The probability $1/4$ is expressed by the amplitude $1/2$ of the normalized good component; this is the exact-success amplification interface.
--
--   Differences from the source:
--   - encoding: equality on all quantum states with clean auxiliaries → literal equality on all complex vectors with clean auxiliaries; reason: linearity makes these conditions equivalent, including preservation of global phase
--   - encoding: O-bounds → positive real gate and auxiliary constants before every register size; reason: this is the family-level asymptotic meaning, with allowable dependence only on the fixed data
--   - encoding: one call each to D,U†,R₀,U → evaluation of the defined four-label word and a count of one for each label; reason: the word denotes precisely the displayed ordered product, without treating U or D as cheap primitive gates
-- source:
--   Chandrima Kayal, Rajat Mittal, Manaswi Paraashar, Nitin Saurabh, STOC 2027 submission #1075 (October 2026), Lemma 2.4, pp. 7–8 (PDF pp. 7–8)

import Definitions.Def_QFTMultiplication_Exact_Model

set_option autoImplicit false

namespace QFTMultiplication.Exact

open QAlgorithms

/-- Lemma 2.4, pp.7–8. The constants bound only R₀. General U and D are abstract
unitaries, with one call each to D,U†,R₀,U in the defined four-call word. -/
theorem one_grover_iterate :
    ∃ Cg Ca : ℝ, 0 < Cg ∧ 0 < Ca ∧ ∀ m : ℕ,
      (∃ (a : ℕ) (c : Circuit baseGates (m + a)),
        CleanImplements c (zeroReflection m) ∧
        (c.size : ℝ) ≤ Cg * m ∧ (a : ℝ) ≤ Ca * m) ∧
      ∀ (U D : Op m) (g h : Vec m),
        U ∈ Matrix.unitaryGroup (Qubits m) ℂ →
        D ∈ Matrix.unitaryGroup (Qubits m) ℂ →
        ‖g‖ = 1 → ‖h‖ = 1 → inner ℂ g h = 0 →
        act U (zeroKet m) = (1 / 2 : ℂ) • g + (Real.sqrt 3 / 2 : ℂ) • h →
        act D g = -g → act D h = h →
        act (groverOperator U D) (act U (zeroKet m)) = g ∧
        (∀ j : Fin 4, groverCalls.count j = 1) := by sorry

end QFTMultiplication.Exact
