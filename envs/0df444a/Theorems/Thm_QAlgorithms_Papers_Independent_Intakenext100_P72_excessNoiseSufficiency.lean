-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P72_excessNoiseSufficiency
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P72.excessNoiseSufficiency
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:46:27.395171+00:00
-- url     : https://prove2.me/theorems/06c2f251-ead1-49bf-8853-b31e2bb5e92a
-- title:
--   Sufficient excess-noise bounds for positive signed model expressions
-- statement:
--   Let $0<G\le1$, $V\ge1$, and $\epsilon\ge0$, and set $\chi=(1-G)/G+\epsilon$. Write $C=\tfrac12\log_2[1/((G\chi+G/V)(G\chi+G))]$ and $E=\tfrac14\log_2[1/(G\chi+G/V)^2]$. Then
--
--   $$
--   \epsilon<\frac{V-1}{2V}\Longrightarrow C>0,\qquad
--   \epsilon<\frac{V-1}{V}\Longrightarrow E>0.
--   $$
--
--   The thresholds tend to $1/2$ and $1$, respectively, as $V\to\infty$. These sufficient conditions hold for every positive lossy transmission, beyond the strong-loss regime surrounding the source paragraph. At $V=1$ neither strict premise can hold for nonnegative excess noise.
--
--   The result concerns explicit signed information-model expressions; the general security interpretation is retained in the deferred paper seed.
-- source:
--   Reverse reconciliation protocols for quantum cryptography with continuous variables, arXiv:quant-ph/0204127v1, PDF p. 5, IV.B: excess-noise tolerance for coherent and EPR protocols

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P72

noncomputable section

open Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P72

/-- Grosshans--Grangier, PDF p.5, IV.B, excess-noise paragraph.
The displayed bounds are sufficient for positivity of the explicit signed
expressions for every lossy transmission. They are not definitions of security. -/
theorem excessNoiseSufficiency
    (G V excess : ℝ) (hG : 0 < G) (hGloss : G ≤ 1)
    (hV : 1 ≤ V) (hexcess : 0 ≤ excess) :
    (excess < coherentExcessThreshold V →
      0 < coherentExpression G ((1 - G) / G + excess) V) ∧
    (excess < eprExcessThreshold V →
      0 < eprExpression G ((1 - G) / G + excess) V) ∧
    Tendsto coherentExcessThreshold atTop (nhds (1 / 2 : ℝ)) ∧
    Tendsto eprExcessThreshold atTop (nhds (1 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P72

end
