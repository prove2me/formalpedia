-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P42_fqrsInnerBound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P42.fqrsInnerBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:14:24.660764+00:00
-- url     : https://prove2.me/theorems/bce2df98-05fc-4cb8-afe9-19afe844c81a
-- title:
--   Unnumbered result: FQRS-derived redistribution inner bound
-- statement:
--   Let $|\psi\rangle^{R\widehat A\widehat B B}$ be a normalized pure state on finite nonzero registers, with Alice initially holding $\widehat A\widehat B$, Bob holding $B$, and inaccessible reference $R$. The goal is to transfer $\widehat B$ to Bob while retaining all other source systems with their original ownership.
--
--   The FQRS construction achieves
--   $$(Q_2,E_2)=\left(\tfrac12 I(\widehat B;RB)_\psi,\tfrac12 I(\widehat B;\widehat A)_\psi\right).$$
--   Communication is one-way quantum communication with arbitrary local CPTP maps; $E$ is input minus output Bell-pair consumption. The IID interpretation uses every positive error and rate slack, all sufficiently large positive blocklengths, and full joint source/reference and final Bell-pair trace-norm reconstruction. Entropies and rates are in bits.
--
--   This is the source's reverse-Shannon inner bound. The construction treats $B$ as reference but retains Bob's $B$ in the output error test.
-- source:
--   Channel simulation with quantum side information, arXiv:quant-ph/0611008v1, PDF p. 18, Unnumbered result: FQRS-derived redistribution inner bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P42

open scoped BigOperators ComplexConjugate ENNReal

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P07

open QAlgorithms.Papers.Independent.Gap48.P20

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability shannon)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.18: FQRS-derived achievable pair, with B included in the joint output
and reference test. Both communication and consumed entanglement have factor 1/2. -/
theorem fqrsInnerBound {A C B R : Type}
    [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    [Nonempty A] [Nonempty C] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) (hpsi : IsState psi) :
    RedistributionAchievable psi (fqrsQuantum psi) (senderMutual psi / 2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P42

end
