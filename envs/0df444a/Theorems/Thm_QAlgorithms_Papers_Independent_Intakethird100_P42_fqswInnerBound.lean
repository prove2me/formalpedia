-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P42_fqswInnerBound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P42.fqswInnerBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:13:34.52967+00:00
-- url     : https://prove2.me/theorems/ce19af06-226c-4f7b-8fec-a729fc59473e
-- title:
--   Unnumbered result: FQSW-derived redistribution inner bound
-- statement:
--   Let $|\psi\rangle^{R\widehat A\widehat B B}$ be a normalized pure state on finite nonzero registers. Initially Alice holds $\widehat A\widehat B$, Bob holds $B$, and $R$ is inaccessible. Alice must transfer $\widehat B$ to Bob while retaining $\widehat A$ and preserving the complete source and reference.
--
--   With one-way qubit communication and arbitrary local CPTP maps, the FQSW construction achieves the rate pair
--   $$(Q_1,E_1)=\left(\tfrac12 I(\widehat B;R\widehat A)_\psi,-\tfrac12 I(B;\widehat B)_\psi\right).$$
--   Here rates and entropies are in bits; $E$ is signed Bell consumption, with distinct natural input and output Bell counts and $E<0$ denoting generation. For every positive error and rate slack, all sufficiently large positive IID blocks have a protocol with full joint source/reference and final Bell-pair trace-norm error within the error tolerance.
--
--   This gives the source's merging-based inner bound. Treating $\widehat A$ as reference in the construction does not remove it from Alice's final output.
-- source:
--   Channel simulation with quantum side information, arXiv:quant-ph/0611008v1, PDF p. 18, Unnumbered result: FQSW-derived redistribution inner bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P42

open scoped BigOperators ComplexConjugate ENNReal

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P07

open QAlgorithms.Papers.Independent.Gap48.P20

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability shannon)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF pp.17--18: FQSW-derived achievable pair. Ahat remains Alice's final
register although this construction treats it as reference. E is NEGATIVE. -/
theorem fqswInnerBound {A C B R : Type}
    [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    [Nonempty A] [Nonempty C] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) (hpsi : IsState psi) :
    RedistributionAchievable psi (mergingClassicalCost psi / 2) (-redistributionReceiverInformation psi / 2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P42

end
