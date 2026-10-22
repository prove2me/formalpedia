-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P30_minimum_output_lower_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P30.minimum_output_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:16:09.409995+00:00
-- url     : https://prove2.me/theorems/b50e8d4c-d873-4bc3-a904-d4301324a704
-- title:
--   Appendix 1: minimum-output-entropy lower bound
-- statement:
--   Let $0\le T\le1$, $G\ge1$, and $M=A_G\circ L_T$ on the complete one-mode Fock space, with both environment modes in vacuum. Let $S$ be extended von Neumann entropy in nats, and set $s_{\rm pure}(A)=\inf_{\|u\|=1}S(A(|u\rangle\langle u|))$ and $s(A)=\inf_{\rho}S(A(\rho))$, where $\rho$ ranges over all normalized positive trace-class operators. Then every such $\rho$ satisfies
--
--   $$
--   S(M(\rho))\ge s_{\rm pure}(A_G).
--   $$
--
--   Consequently $s_{\rm pure}(M)\ge s_{\rm pure}(A_G)$ and $s(M)\ge s(A_G)$. No infimum is assumed attained and infinite entropies are allowed.
--
--   This is the uniform lower bound used in the single-use reduction. The displayed calculation uses entropy concavity, although the explanatory text calls its third step sub-additivity.
-- source:
--   Majorization theory approach to the Gaussian channel minimum entropy conjecture, arXiv:1111.1986v1, PDF p. 4, Appendix 1, (A.1)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P30

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- arXiv:1111.1986v1, PDF pp.4-5, (A.1). The lower bound holds for every
input, not just a manufactured optimizer. Both printed minima are interpreted
as infima, and entropy may be infinite. Step (3) is concavity, not the printed
'sub-additivity'. -/
theorem minimum_output_lower_bound (T G : ℝ) (hT : 0 ≤ T) (hTu : T ≤ 1) (hG : 1 ≤ G) :
    (∀ X : D.FockOperator, D.IsDensity X →
      C.pureMinimumEntropy (C.amplifier G) ≤ C.fockEntropyNats (C.amplifier G (loss T X))) ∧
    C.pureMinimumEntropy (C.amplifier G) ≤
      C.pureMinimumEntropy (fun X => C.amplifier G (loss T X)) ∧
    C.minimumEntropy (C.amplifier G) ≤
      C.minimumEntropy (fun X => C.amplifier G (loss T X)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P30

end
