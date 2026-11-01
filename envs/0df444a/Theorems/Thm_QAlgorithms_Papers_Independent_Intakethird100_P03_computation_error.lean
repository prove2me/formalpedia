-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_computation_error
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.computation_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:55:32.525729+00:00
-- url     : https://prove2.me/theorems/23d2d1d3-8e96-46b9-9dc5-79784aa18ae1
-- title:
--   Lemma 5: gate precision and computation error
-- statement:
--   Suppose $L$ unitary operations compute a promised function with worst-case error at most $0\le\epsilon<1/2$, using clean initial work and a specified output register. Replace each operation by a unitary within phase-sensitive operator distance $\delta\ge0$. For every promised input,
--
--   $$
--   \Pr[\text{correct output after replacement}]\ge1-(\epsilon+2L\delta).
--   $$
--
--   The bound is retained even when its right side is nonpositive or the resulting error exceeds one half.
--
--   Only the output register is measured, and both operation lists are specified on the actual computer memory.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 12, Lemma 5: gate precision and computation error

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.12, Lemma 5: gate errors imply a worst-case success bound on every valid
input, including when the resulting upper bound on error exceeds one half or one. -/
theorem computation_error {n m w L : ℕ}
    (U V : Fin L → Matrix (Qubits (n + w)) (Qubits (n + w)) ℂ)
    (out : Fin m ↪ Fin (n + w)) (N : Set (Qubits n)) (F : Qubits n → Qubits m)
    (epsilon delta : ℝ) (he : 0 ≤ epsilon) (hehalf : epsilon < 1 / 2) (hd : 0 ≤ delta)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Qubits (n + w)) ℂ)
    (hV : ∀ j, V j ∈ Matrix.unitaryGroup (Qubits (n + w)) ℂ)
    (herror : Computes (orderedProd U) out N F epsilon)
    (happrox : ∀ j, specNorm (V j - U j) ≤ delta) :
    Computes (orderedProd V) out N F (epsilon + 2 * (L : ℝ) * delta) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
