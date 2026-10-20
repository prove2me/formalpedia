-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P29_amplifier_highEnergyLimit
-- name    : QAlgorithms.Papers.Independent.Dependency50.P29.amplifier_highEnergyLimit
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:29:41.101841+00:00
-- url     : https://prove2.me/theorems/b2245b3c-5fe2-4e6c-8d3b-36e0c3147635
-- title:
--   High-energy limit of the quantum-limited amplifier expression
-- statement:
--   Let $g(x)=(x+1)\log_2(x+1)-x\log_2x$ for $x\ge0$, with $0\log_2 0=0$. For gain $\kappa\ge1$, set $a_\kappa(s)=g(\kappa s+\kappa-1)-g((\kappa-1)(s+1))$. For every $\kappa>1$,
--
--   $$\lim_{s\to+\infty}a_\kappa(s)=\log_2\!\left(\frac{\kappa}{\kappa-1}\right).$$
--
--   At $\kappa=1$, $a_1(s)=g(s)$ tends to $+\infty$. These limits concern the formula itself, rather than an operational definition of unconstrained capacity.
--
--   The paper records this as consistent with [27] and with the results of [29,30]. The identity case is the extended-value interpretation of the singular printed logarithm.
-- source:
--   Energy-constrained private and quantum capacities of quantum channels, arXiv:1609.01997v2, PDF p. 24, Unnumbered Eq.334: high-energy quantum-limited amplifier limit

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P29

open Filter

-- PDF p.2, Eq.(2): reuse the accepted entropy in bits; its complete body
-- implements the same zero-occupation convention as this paper.

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF p.24, Eq.(334): high-energy limit of Eq.(333), including its identity endpoint.
The finite formula is asserted for `gain > 1`; at `gain = 1` the limit is positive infinity.
This records the limit of the displayed expression, with provenance [27,29,30],
and does not define or identify an unconstrained operational capacity. -/
theorem amplifier_highEnergyLimit :
    (∀ gain : ℝ, 1 < gain →
      Tendsto (amplifierFormula gain) atTop
        (nhds (Real.log (gain / (gain - 1)) / Real.log 2))) ∧
    Tendsto (amplifierFormula 1) atTop atTop := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P29

end
