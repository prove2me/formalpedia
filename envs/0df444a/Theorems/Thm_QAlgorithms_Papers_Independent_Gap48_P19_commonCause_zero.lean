-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P19_commonCause_zero
-- name    : QAlgorithms.Papers.Independent.Gap48.P19.commonCause_zero
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:06:55.215988+00:00
-- url     : https://prove2.me/theorems/fcc641c3-c7b9-4cf9-9f02-d0a984104fb7
-- title:
--   Common-cause classical laws have zero CMI
-- statement:
--   Let $A,B,L$ be finite nonempty alphabets. Let $w$ be a probability law on $L$, and let $k_A(a\mid l)$ and $k_B(b\mid l)$ be probability kernels, normalized for every $l$. Define $p(a,b,l)=k_A(a\mid l)k_B(b\mid l)w(l)$. With Shannon entropy in nats and the nonnegative convention for conditional mutual information,
--
--   $$I_p(A:B\mid L)=H_p(AL)+H_p(BL)-H_p(L)-H_p(ABL)=0.$$
--
--   Zero probabilities and zero mixture weights are allowed. This is the common-cause construction used in the classical comparison.
-- source:
--   Entanglement of Distillation and Conditional Mutual Information, arXiv:quant-ph/0202144v2, PDF p. 3, §2, Eq.(5)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19

namespace QAlgorithms.Papers.Independent.Gap48.P19

open scoped ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, (5): normalized common-cause laws have zero CMI.
The corrected CMI sign is documented in the module preamble. -/
theorem commonCause_zero {A B L : Type} [Fintype A] [Fintype B] [Fintype L]
    [Nonempty A] [Nonempty B] [Nonempty L]
    (w : L → ℝ) (ka : L → A → ℝ) (kb : L → B → ℝ)
    (hw : IsLaw w) (ha : IsKernel ka) (hb : IsKernel kb) :
    extensionClassicalCMI (commonCause w ka kb) = 0 := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P19
