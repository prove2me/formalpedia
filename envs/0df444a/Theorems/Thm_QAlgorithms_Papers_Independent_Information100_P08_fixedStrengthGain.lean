-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_fixedStrengthGain
-- name    : QAlgorithms.Papers.Independent.Information100.P08.fixedStrengthGain
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:16:50.861984+00:00
-- url     : https://prove2.me/theorems/b33e88ee-5b83-4e86-aae0-b53efb51aaa7
-- title:
--   Fixed-strength explicit two-round gain
-- statement:
--   Write $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, with the continuous $0\log0=0$ convention, and $H(v)=h_2((1-\sqrt{1-4v})/2)$ for $0\le v\le1/4$. For real strength $s$ near $0$ and noise $p\in[0,1]$, define the scalar function $$r_2(p,s)=1-h_2\!\left(\frac{1+(1-p)s}{2}\right)+h_2\!\left(\frac{1+s}{2}\right)-h_2\!\left(\frac{1+\sqrt{(1-p)^2+[1-(1-p)^2]s^2}}2\right).$$ At noise $p=1/2$ and strength $s=4/5$, $$r_2(1/2,4/5)=1-h_2(7/10)+h_2(9/10)-h_2\!\left(\frac{10+\sqrt{73}}{20}\right)>1-h_2(1/4).$$ This is the exact fixed-strength scalar improvement. The source's trailing decimals are illustrative, and this statement makes no global family-optimality claim.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 56, Fixed-strength explicit two-round gain

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF p.56, (12.16): the exact radical and strict fixed-strength gain; trailing decimals
in the paper are illustrative, and no global optimization claim is made here. -/
theorem fixedStrengthGain :
    twoRoundRate (1 / 2) (4 / 5) =
      1 - binEntropy2 (7 / 10) + binEntropy2 (9 / 10) - binEntropy2 ((10 + Real.sqrt 73) / 20) ∧
    1 - binEntropy2 (1 / 4) < twoRoundRate (1 / 2) (4 / 5) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
