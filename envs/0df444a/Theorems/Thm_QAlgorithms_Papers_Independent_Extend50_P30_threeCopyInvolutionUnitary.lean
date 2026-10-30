-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_threeCopyInvolutionUnitary
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.threeCopyInvolutionUnitary
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:32:45.133999+00:00
-- url     : https://prove2.me/theorems/b1cd3b27-e9b1-4412-9d6f-4a3d2b94aeb4
-- title:
--   Three-copy phase-point involution
-- statement:
--   Let $d\geq2$ satisfy $d\equiv1$ or $5\pmod6$. For every $n\geq0$, the operator below on three copies of $n$ qudits is Hermitian and unitary. The local dimension need not be prime.
--
--   $$
--   V=d^{-n}\sum_xA_x^{\otimes3},\qquad V^\dagger=V,\quad V^\dagger V=I.
--   $$
--
--   This gives the source's three-copy phase-point involution in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 61, lemma-8.5

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.61, Lemma 8.5: both 2 and 3 are invertible; no prime hypothesis is added. -/
theorem threeCopyInvolutionUnitary (d n : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hmod : d % 6 = 1 ∨ d % 6 = 5) :
    (threeCopyInvolution d n).IsHermitian ∧
      threeCopyInvolution d n ∈ Matrix.unitaryGroup (QuditCopies d n 3) ℂ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
