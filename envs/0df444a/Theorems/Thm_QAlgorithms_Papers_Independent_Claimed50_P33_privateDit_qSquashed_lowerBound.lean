-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_privateDit_qSquashed_lowerBound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.privateDit_qSquashed_lowerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:48:03.914378+00:00
-- url     : https://prove2.me/theorems/c93c5144-0259-4316-a926-fd505442ae0b
-- title:
--   Observation 1: private dits have at least m log d q-squashed total correlation
-- statement:
--   Let $m\ge2$, $d\ge1$, let $\tau$ be any normalized shield state on finite nonzero local shield registers, and let $U_0,\ldots,U_{d-1}$ be arbitrary unitaries on the joint shield. Form the private dit with local key dimension $d$,
--
--   $$\gamma_m^{(d)}=\frac1d\sum_{a,b=0}^{d-1}|a\cdots a\rangle\langle b\cdots b|\otimes U_a\tau U_b^\dagger.$$
--
--   Its unrestricted TOTAL-information quantum squashed entanglement satisfies
--
--   $$E_{I_m}^q(\gamma_m^{(d)})\ge m\log_2d.$$
--
--   There is no factor $1/2$, and the shield may itself be entangled. At $d=1$ only the lower bound zero is asserted. This is the private-state normalization needed for the total-information key upper bound.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 9, Observation 1: private dits have at least m log d q-squashed total correlation

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Observation 1, PDF pp.9–10,(78)–(81): the TOTAL-information q version
on constructed private dits. At d=1 the shield need not have zero entanglement. -/
theorem privateDit_qSquashed_lowerBound {m : ℕ} (hm : 2 ≤ m)
    {H : Fin m → Type} [∀ i, Fintype (H i)] [∀ i, Nonempty (H i)]
    (d : ℕ) (hd : 0 < d) (tau : Matrix (RegisterBasis H) (RegisterBasis H) ℂ)
    (htau : IsDensityMatrix tau) (U : Fin d → Matrix.unitaryGroup (RegisterBasis H) ℂ) :
    (m : ℝ) * Real.logb 2 d ≤ multipartiteSquashed false .total (privateDit d tau U) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
