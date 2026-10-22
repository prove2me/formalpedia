-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P25_bellErrorRate
-- name    : QAlgorithms.Papers.Independent.Gap48.P25.bellErrorRate
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:50:22.924004+00:00
-- url     : https://prove2.me/theorems/78f1e085-993f-4d92-8b57-b1217794deb4
-- title:
--   Appendix B.2.b: Bell-measurement error and repeater yield, Eq.(B3)
-- statement:
--   Let $R_2\ge0$ be the mean-cycle detection rate and let $F\in[0,1]$ be the Bell measurement fidelity. The desired Bell state has probability $F$ and each other Bell state has probability $(1-F)/3$. One wrong Bell state preserves the bit correlation and the other two reverse it. The error and assigned signed one-way perfect-EC toy yield are
--
--   $$\varepsilon={2\over3}(1-F),\qquad K_2=R_2[1-2h(\varepsilon)],\qquad K_2^+=R_2\max\{1-2h(\varepsilon),0\}.$$
--
--   There is a unique $q_*\in(0,1/2)$ with $h(q_*)=1/2$. In the useful branch $F\ge1/4$, $K_2>0$ exactly when $R_2>0$ and $F>1-3q_*/2$. This gives the source's threshold implicitly, without treating its approximate 83.5 percent decimal as exact.
-- source:
--   The Security of Practical Quantum Key Distribution, arXiv:0802.4155v3, PDF p. 47, Appendix B.2.b: Bell-measurement error and repeater yield, Eq.(B3)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P25

open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eq.(B3), PDF p.47: computed Bell error and assigned mean-cycle yield.
The approximate decimal threshold is replaced by its implicit entropy definition. -/
theorem bellErrorRate (R F : ℝ) (hR : 0 ≤ R) (hF : F ∈ Set.Icc (0 : ℝ) 1) :
    (∀ i, 0 ≤ bellLaw F i) ∧ (∑ i : Fin 4, bellLaw F i) = 1 ∧
    bellError F = (2/3)*(1-F) ∧
    repeaterKey R F = R*(1-2*QAlgorithms.binEntropy2 ((2/3)*(1-F))) ∧
    max (repeaterKey R F) 0 = R*max (1-2*QAlgorithms.binEntropy2 ((2/3)*(1-F))) 0 ∧
    ∃ q : ℝ, 0 < q ∧ q < 1/2 ∧ QAlgorithms.binEntropy2 q = 1/2 ∧
      (∀ z : ℝ, z ∈ Set.Icc (0 : ℝ) (1/2) → (QAlgorithms.binEntropy2 z = 1/2 ↔ z = q)) ∧
      (1/4 ≤ F → (0 < repeaterKey R F ↔ 0 < R ∧ 1-(3/2)*q < F)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P25

end
