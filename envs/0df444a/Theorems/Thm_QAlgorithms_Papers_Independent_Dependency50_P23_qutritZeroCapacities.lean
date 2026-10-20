-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_qutritZeroCapacities
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.qutritZeroCapacities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:51:40.91901+00:00
-- url     : https://prove2.me/theorems/4ca45e76-c44e-4bd8-8408-b7132d7089d3
-- title:
--   Unnumbered result: zero-error private/classical versus quantum capacities
-- statement:
--   Let $0<\alpha\le\pi/4$, and let $\mathcal N_\alpha$ be the qutrit channel of §V.C, with its fixed two-dimensional complementary environment. Write $Q_0,P_0,C_0$ for unassisted quantum, private classical and classical zero-error capacities, respectively, obtained by regularizing exact finite-block codes. Then
--
--   $$Q_0(\mathcal N_\alpha)<1=P_0(\mathcal N_\alpha)=C_0(\mathcal N_\alpha).$$
--
--   Exact private codes have joint output equal to a perfectly correlated classical key tensor a common environment state; exact quantum codes transmit entanglement with fidelity one. These zero-error quantities are distinct from their vanishing-error counterparts.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 22, Unnumbered result

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (log2 quantumCapacity)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- PDF p.22, unnumbered result: exact zero-error quantum/private/classical
capacities. These regularize exact finite-block codes, not vanishing-error codes. -/
theorem qutritZeroCapacities (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha ≤ Real.pi/4) :
    quantumZeroCapacity (qutrit alpha) < 1 ∧ privateZeroCapacity alpha = 1 ∧
    uaZeroCapacity (qutrit alpha) = 1 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
