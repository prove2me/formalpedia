-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P29_pureLoss_highEnergyLimit
-- name    : QAlgorithms.Papers.Independent.Dependency50.P29.pureLoss_highEnergyLimit
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:28:51.862628+00:00
-- url     : https://prove2.me/theorems/27fb769f-46d6-4091-82b2-ea0db54de2d9
-- title:
--   High-energy limit of the pure-loss expression
-- statement:
--   Let $g(x)=(x+1)\log_2(x+1)-x\log_2x$ for $x\ge0$, with $0\log_2 0=0$, and set $f_\eta(s)=g(\eta s)-g((1-\eta)s)$. For each transmissivity $1/2\le\eta<1$,
--
--   $$\lim_{s\to+\infty}f_\eta(s)=\log_2\!\left(\frac{\eta}{1-\eta}\right).$$
--
--   At the identity endpoint $\eta=1$, $f_1(s)=g(s)$ tends to $+\infty$. All logarithms in the displayed formulas are in bits. These are limits of the source's scalar expressions; they do not define an unconstrained operational capacity.
--
--   The source connects the finite expression to [27]. The divergent endpoint makes explicit the extended-value interpretation of its singular logarithm.
-- source:
--   Energy-constrained private and quantum capacities of quantum channels, arXiv:1609.01997v2, PDF p. 24, Unnumbered Eq.332: high-energy limit for degradable pure loss

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P29

open Filter

-- PDF p.2, Eq.(2): reuse the accepted entropy in bits; its complete body
-- implements the same zero-occupation convention as this paper.

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF p.24, Eq.(332): high-energy limit of Eq.(331), including its identity endpoint.
For `1/2 ≤ eta < 1` the limit is the stated finite base-two logarithm.
At `eta = 1` the formula is `g(occupation)` and diverges to positive infinity;
this is the extended-value reading of the printed singular logarithm, not real division by zero.
The paper relates this limit to [27]; no independent operational capacity formula is assumed. -/
theorem pureLoss_highEnergyLimit :
    (∀ eta : ℝ, (1 / 2 : ℝ) ≤ eta → eta < 1 →
      Tendsto (lossFormula eta) atTop
        (nhds (Real.log (eta / (1 - eta)) / Real.log 2))) ∧
    Tendsto (lossFormula 1) atTop atTop := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P29

end
