-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P30_vacuum_heralded_reduction
-- name    : QAlgorithms.Papers.Independent.Gap48.P30.vacuum_heralded_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:21:23.388161+00:00
-- url     : https://prove2.me/theorems/a65383cc-9afc-4699-a168-478d5918518d
-- title:
--   Appendix 5c/Figure 3: heralded two-mode vacuum squeezing reduction
-- statement:
--   Let $0<\lambda<1$ and $0\le T<1$. Alice and Bob initially share the two-mode squeezed vacuum $|\Psi_\lambda^{(0)}\rangle$. Bob mixes his mode with a vacuum ancillary mode on a beam splitter of intensity transmissivity $T$ and counts the reflected photons. Let $v_0$ denote the unnormalized branch for zero reflected photons, formed with the actual local splitter Kraus operator. Then
--
--   $$
--   P_0=\|v_0\|^2=\frac{1-\lambda^2}{1-T\lambda^2},\qquad
--   v_0=\sqrt{P_0}\,|\Psi_{\sqrt{T}\lambda}^{(0)}\rangle,\qquad 0<P_0<1.
--   $$
--
--   The splitter and its local tensor operation realize their physical matrices. Conditioned on the zero-count event, the target squeezing is $\lambda'=\sqrt T\lambda$.
--
--   This is a heralded transformation. The probability printed immediately before (A.59) is inverted; the corrected ratio follows from the displayed branch norm and from (A.62) with $k=l=0$.
-- source:
--   Majorization theory approach to the Gaussian channel minimum entropy conjecture, arXiv:1111.1986v1, PDF p. 10, Figure 3; (A.57)–(A.59)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P30

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- arXiv:1111.1986v1, PDF pp.9-10, Figure 3 and (A.57)-(A.59).
The printed zero-count probability N(sqrt(T)lambda)^2/N(lambda)^2 is corrected
to its reciprocal, forced by the displayed unnormalized branch and by A.62
with k=ell=0. This is heralded, not deterministic. -/
theorem vacuum_heralded_reduction (lambda T : ℝ)
    (hl : 0 < lambda) (hlu : lambda < 1) (hT : 0 ≤ T) (hTu : T < 1) :
    D.AttenuatorRealized (Real.sqrt T) ∧
    TensorRealized 1 (D.attenuatorKraus (Real.sqrt T) 0) ∧
    let P := (1 - lambda ^ 2) / (1 - T * lambda ^ 2)
    0 < P ∧ P < 1 ∧ ‖countBranch 0 lambda T 0‖ ^ 2 = P ∧
    countBranch 0 lambda T 0 = (Real.sqrt P : ℂ) • squeezed 0 (Real.sqrt T * lambda) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P30

end
