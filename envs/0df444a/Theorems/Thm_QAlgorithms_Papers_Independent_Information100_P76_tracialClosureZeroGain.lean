-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P76_tracialClosureZeroGain
-- name    : QAlgorithms.Papers.Independent.Information100.P76.tracialClosureZeroGain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:03:42.193065+00:00
-- url     : https://prove2.me/theorems/c13cf5be-5545-4420-ac59-4e5773af4116
-- title:
--   Section 8, unnumbered: tracial approximation closure implies zero kappa
-- statement:
--   Let $\Phi$ be CPTP on $\mathbb C^q$, $q\ge1$. A finite weighted-tracial dilation has finitely many sectors of positive dimensions $d_j$, nonnegative weights $p_j$ summing to one, independent sector initializer $\pi_{d_j}=I/d_j$, and sector-preserving unitary blocks $U_j$. Its channel is $\sum_jp_j\operatorname{Tr}_{B_j}[U_j(\rho\otimes\pi_{d_j})U_j^*]$. If such channels approximate $\Phi$ arbitrarily well in half diamond distance, then
--
--   $$\kappa(\Phi)=0.$$
--
--   All sector dimensions and weights count in the finite dilation. This is a forward implication from approximation closure; it asserts neither a converse nor an attained finite tracial dilation.
-- source:
--   Bath dimension and initial entropy for closed repeated use of a quantum channel, arXiv:2609.18267v1, PDF p. 15, Section 8, unnumbered

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P76

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open Filter

/-- PDF p.15, Section 8: finite weighted-tracial approximation implies zero kappa.
The converse is explicitly not asserted by the source. -/
theorem tracialClosureZeroGain {q : ℕ} (hq : 0 < q)
    (Phi : Superop (Fin q) (Fin q)) (hPhi : IsChannel Phi)
    (hclosure : inWeightedTracialClosure Phi) : intrinsicCost Phi = 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P76

end
