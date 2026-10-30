-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_quditInvolutionUnitary
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.quditInvolutionUnitary
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:00:04.018029+00:00
-- url     : https://prove2.me/theorems/57ba9072-6142-447e-9e92-f6daeb53e6ac
-- title:
--   Hermitian qudit testing involution
-- statement:
--   Let $d\geq2$, $n\geq0$, and let $s$ be a nonnegative tensor exponent coprime to $d$. Using the Weyl phases of the source, the operator $V_s$ on $2s$ copies is Hermitian and unitary.
--
--   $$
--   V_s=d^{-n}\sum_{x\in\mathcal V_n}(W_x\otimes W_x^\dagger)^{\otimes s},\qquad V_s^\dagger=V_s,\quad V_s^\dagger V_s=I.
--   $$
--
--   This gives the source's hermitian qudit testing involution in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 24, lemma-3.8

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.24, Lemma 3.8: s is a natural tensor exponent, invertible modulo d. -/
theorem quditInvolutionUnitary (d n s : ℕ) [NeZero d] (hd : 2 ≤ d) (hs : Nat.Coprime s d) :
    (quditInvolution d n s).IsHermitian ∧
      quditInvolution d n s ∈ Matrix.unitaryGroup (QuditCopies d n (2 * s)) ℂ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
