-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma3_haarKhintchine
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma3_haarKhintchine
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:46:34.745475+00:00
-- url     : https://prove2.me/theorems/5b8a7b3a-0fb7-4337-b19e-acc2b2503d72
-- title:
--   Lemma 3 (Khintchine inequality for homogeneous 1-local observables). Let 𝑛 ≥ 1. Consider |𝜓⟩ = 𝑖=1 |𝜓𝑖 ⟩ where |𝜓𝑖 ⟩ is a single-qubit Haar-random pure state
-- statement:
--   Let $n\ge1$, and let $O$ be a Hermitian homogeneous one-local observable. Let $|\psi\rangle=\bigotimes_{i=1}^n|\psi_i\rangle$, with independent Haar-distributed single-qubit pure states. With ordinary trace,
--   $$\frac1{\sqrt6}\sqrt{\frac{\operatorname{tr}(O^2)}{2^n}}\le\mathbb E|\langle\psi|O|\psi\rangle|\le\frac1{\sqrt3}\sqrt{\frac{\operatorname{tr}(O^2)}{2^n}}.$$
--   This bounds an average absolute energy by the normalized Frobenius scale.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 25, Lemma 3 (Khintchine inequality for homogeneous 1-local observables). Let 𝑛 ≥ 1. Consider |𝜓⟩ = 𝑖=1 |𝜓𝑖 ⟩ where |𝜓𝑖 ⟩ is a single-qubit Haar-random pure state

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Lemma 3, paper p.25, A42, with independent one-qubit Haar pure states. -/
theorem lemma3_haarKhintchine (n : ℕ) (hn : 1 ≤ n)
    (O : (Matrix (Qubits n) (Qubits n) ℂ)) (hO : O.IsHermitian) (hhom : IsHomogeneous 1 O) :
    let rms := Real.sqrt ((O * O).trace.re / (2 : ℝ) ^ n)
    let avg := ∫ u, |effectProb O (namedWireTensor (fun i : Fin n => haarQubit (u i)))|
      ∂haarProductLaw (Fin n)
    rms / Real.sqrt 6 ≤ avg ∧ avg ≤ rms / Real.sqrt 3 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
