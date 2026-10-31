-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P20_pure_source_coding_rates
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P20.pure_source_coding_rates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:33:54.202163+00:00
-- url     : https://prove2.me/theorems/043ad5d5-fcf2-4930-8d1e-f1039147b470
-- title:
--   Theorem 1: four pure-source coding rates equal entropy
-- statement:
--   Let $p_i$ be a discrete probability law on an arbitrary label set and let $\rho_i$ be normalized pure states on a nonzero finite-dimensional complex space. Set $\rho_p=\sum_i p_i\rho_i$. At each positive block length use the independent product probabilities and tensor product states. A blind encoder and decoder are CPTP; a visible encoder maps labels to memory density matrices and has a CPTP decoder. Each memory has a positive finite dimension. Define the ordinary blind and visible rates as the infima of $\limsup_n n^{-1}\log\dim K_n$ over code sequences whose average overlap errors tend to zero. Define their converse rates by replacing error convergence with $\liminf_n\epsilon_n<1$. Then
--
--   $$R_B=R_V=R_B^-=R_V^-=H(\rho_p),\qquad H(\rho)=-\operatorname{Tr}\rho\log\rho.$$
--
--   All logarithms are natural. Infima and memory-rate limits are in the extended reals; no full-rank or finite-label hypothesis is added.
-- source:
--   Exponents of quantum fixed-length pure state source coding, arXiv:quant-ph/0202002v6, PDF p. 2, Theorem 1, (1)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P20

noncomputable section

open scoped Matrix ENNReal ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P20

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P47 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P53 (SpectralData)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Dependency50.P28 (classicalD)

attribute [local instance] Classical.propDecidable

/-- Theorem 1, PDF p.2, (1): all four pure-source rates equal the entropy
of the computed average. This is a statement of Hayashi's cited known result;
no equivalence with a fixed-error library theorem is assumed as a hypothesis. -/
theorem pure_source_coding_rates {L : Type*} {d : ℕ} (S : DiscretePureSource L d) :
    let H := (QAlgorithms.Papers.Independent.Information100.P56.entropy S.average : EReal)
    blindMinimumRate S false = H ∧
    visibleMinimumRate S false = H ∧
    blindMinimumRate S true = H ∧
    visibleMinimumRate S true = H := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P20

end
