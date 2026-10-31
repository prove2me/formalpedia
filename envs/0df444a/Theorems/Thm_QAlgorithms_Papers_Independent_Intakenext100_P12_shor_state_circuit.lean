-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_shor_state_circuit
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.shor_state_circuit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:15:49.694212+00:00
-- url     : https://prove2.me/theorems/1af80103-2091-42ec-932c-254d93d8954c
-- title:
--   §XI.C (150)–(154), Fig.7: finite Shor-state circuit
-- statement:
--   Use the paper's $S=\operatorname{diag}(e^{-i\pi/8},e^{i\pi/8})$ and the chronological Fig.7 decompositions. The explicitly defined three-qubit circuit contains exactly five $S$, four $S^{-1}$, and eight CNOT gates, counted from its own gate list. Its matrix is
--
--   $$U=e^{-i\pi/8}\operatorname{CCZ},\qquad\operatorname{CCZ}|a,b,c\rangle=(-1)^{abc}|a,b,c\rangle.$$
--
--   On $|+\rangle^{\otimes3}$ it prepares, up to this global phase, $2^{-3/2}\sum_{a,b,c}(-1)^{abc}|a,b,c\rangle$. This vector spans the simultaneous $+1$ eigenspace of $\operatorname{CZ}_{12}X_3$ and its cyclic permutations.
--
--   The gate counts are tied to the actual matrix-evaluated circuit.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 18, §XI.C (150)–(154), Fig.7: finite Shor-state circuit

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section XI.C (150)–(154), Fig.7, PDF pp.18–19: exact finite Shor-state circuit.
The source S phases are retained, so the resulting global phase is exp(-i*pi/8). -/
theorem shor_state_circuit :
    (∀ k : Fin 3, (shorStabilizer k).mulVec shorState = shorState) ∧
    (∀ psi : (Fin 3 → Bool) → ℂ,
      (∀ k : Fin 3, (shorStabilizer k).mulVec psi = psi) ↔ ∃ c : ℂ, psi = c • shorState) ∧
    shorWord.countP (fun g => match g with | .phase false _ => true | _ => false) = 5 ∧
    shorWord.countP (fun g => match g with | .phase true _ => true | _ => false) = 4 ∧
    shorWord.countP (fun g => match g with | .cx _ _ => true | _ => false) = 8 ∧
    shorEval shorWord = cisPhase (-Real.pi / 8) • ccz ∧
    (∀ b : Fin 3 → Bool,
      (shorEval shorWord).mulVec (fun _ => (Real.sqrt 8 : ℂ)⁻¹) b =
        cisPhase (-Real.pi / 8) *
          (if b 0 && b 1 && b 2 then -1 else 1) / (Real.sqrt 8 : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
