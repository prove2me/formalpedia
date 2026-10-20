-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_amplitudeDampingEASeparation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.amplitudeDampingEASeparation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:44:33.441422+00:00
-- url     : https://prove2.me/theorems/576d28d2-60be-40bb-bd03-403d38943c89
-- title:
--   Unnumbered remark/Fig.5: amplitude-damping separation from EA
-- statement:
--   Let $0\le\gamma\le3/4$, and let $\mathcal N_\gamma^{\mathrm{AD}}$ be the qubit amplitude-damping channel with Kraus matrices $\operatorname{diag}(1,\sqrt{1-\gamma})$ and $\sqrt\gamma|0\rangle\langle1|$. Then
--
--   $$C_\beta(\mathcal N_\gamma^{\mathrm{AD}})<C_E(\mathcal N_\gamma^{\mathrm{AD}}).$$
--
--   Here $C_E$ is operational entanglement-assisted classical capacity and $C_\beta$ is the logarithm of Eq.(45)'s program. This records precisely the interval claimed in the remark and Fig.5, without extending the numerical claim to a larger interval.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 18, Unnumbered remark/Fig.5

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

/-- PDF p.18, Remark and Fig.5: precisely the plotted interval 0≤gamma≤3/4. -/
theorem amplitudeDampingEASeparation (gamma : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 3/4) :
    cBeta (AD gamma) < eaCapacity (AD gamma) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
