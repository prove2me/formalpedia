-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_qutritLovaszSeparation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.qutritLovaszSeparation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:50:57.326728+00:00
-- url     : https://prove2.me/theorems/f1bf55cc-9840-4567-b6f4-c722eae2720f
-- title:
--   Proposition 18: stricter bound than the naive Lovasz number
-- statement:
--   Let $0<\alpha\le\pi/4$, and let $\mathcal N_\alpha$ be the qutrit channel with the two Kraus operators of §V.C. For a Kraus family $E_i$, let $S=\operatorname{span}\{E_i^\dagger E_j\}$, and define the naive Lovasz number by the attained maximum $\vartheta(\mathcal N)=\max\{\|I+T\|_\infty:T\in S^\perp,\ I+T\succeq0\}$, using Hilbert–Schmidt orthogonality. Then
--
--   $$M_{0,\mathrm{NS}\cap\mathrm{PPT}}(\mathcal N_\alpha)<\vartheta(\mathcal N_\alpha).$$
--
--   The first quantity is a continuous zero-error message relaxation; the norm is spectral. This exhibits a stricter one-shot converse than the naive Lovasz bound on this family.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 22, Proposition 18

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (log2 quantumCapacity)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- PDF p.22, Proposition 18: strict comparison with the naive Lovasz number. -/
theorem qutritLovaszSeparation (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha ≤ Real.pi/4) :
    zeroMessages true (qutrit alpha) < lovasz (qutrit alpha) ∧
    IsGreatest (lovaszValues (qutrit alpha)) (lovasz (qutrit alpha)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
