-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_smallStrengthExpansion
-- name    : QAlgorithms.Papers.Independent.Information100.P08.smallStrengthExpansion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:16:17.553043+00:00
-- url     : https://prove2.me/theorems/5500bade-7627-47ee-b539-65587c191337
-- title:
--   Small-strength expansion
-- statement:
--   Write $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, with the continuous $0\log0=0$ convention, and $H(v)=h_2((1-\sqrt{1-4v})/2)$ for $0\le v\le1/4$. For real strength $s$ near $0$ and noise $p\in[0,1]$, define the scalar function $$r_2(p,s)=1-h_2\!\left(\frac{1+(1-p)s}{2}\right)+h_2\!\left(\frac{1+s}{2}\right)-h_2\!\left(\frac{1+\sqrt{(1-p)^2+[1-(1-p)^2]s^2}}2\right).$$ Fix $0<p<1$, put $q=1-p$, and define $A(p)=\frac{1-q^2}{2\ln2}(\operatorname{atanh}(q)/q-1)$, with $\operatorname{atanh}(q)=\frac12\ln((1+q)/(1-q))$. Then $A(p)>0$ and $$r_2(p,s)=1-h_2(p/2)+A(p)s^2+O(s^4)\quad(s\to0).$$ Explicitly, there are constants $C>0$ and $0<\delta\le1$, allowed to depend on $p$, such that the absolute remainder is at most $C|s|^4$ whenever $|s|\le\delta$. This supplies the local analytic gain without a uniform-in-$p$ remainder claim.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 56, Small-strength expansion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF p.56, (12.14): fourth-order remainder near zero with p-dependent constants, and
strict positivity of the quadratic coefficient. Endpoints p=0,1 are excluded. -/
theorem smallStrengthExpansion (p : ℝ) (hp : 0 < p) (hpUpper : p < 1) :
    0 < gainCoefficient p ∧
    ∃ C > (0 : ℝ), ∃ delta > (0 : ℝ), delta ≤ 1 ∧ ∀ s : ℝ, |s| ≤ delta →
      |twoRoundRate p s - (1 - binEntropy2 (p / 2) + gainCoefficient p * s ^ 2)| ≤ C * |s| ^ 4 := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
