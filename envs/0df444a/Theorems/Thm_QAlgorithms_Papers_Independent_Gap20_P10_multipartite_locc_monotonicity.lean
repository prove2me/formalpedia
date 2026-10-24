-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P10_multipartite_locc_monotonicity
-- name    : QAlgorithms.Papers.Independent.Gap20.P10.multipartite_locc_monotonicity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:33:55.394723+00:00
-- url     : https://prove2.me/theorems/f979b92f-c8e4-4989-9315-f4eb7fe899e9
-- title:
--   Multipartite LOCC monotonicity
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, all states are positive semidefinite with trace one, and entropies use base-two logarithms with zero eigenvalues contributing zero. Write $E_I$ for one half the infimum of the paired mutual-information increment over all normalized extensions with the required unprimed marginal and arbitrary positive finite primed dimensions.
--
--   Let $n\ge2$, let $\rho$ be an $n$-party state, and let $\sigma$ be the deterministic output of any finite adaptive LOCC protocol retaining these $n$ party labels. Each party’s positive local output dimension may differ from its input dimension. For the multipartite CEMI defined using total information and the prefactor $1/2$,
--
--   $$E_I(\sigma)\le E_I(\rho).$$
--
--   This states monotonicity of the actual multipartite construction; no monotonicity premise is imposed on the functional and no $1/n$ rescaling is substituted.
-- source:
--   An additive and operational entanglement measure: conditional entanglement of mutual information, arXiv:0804.3683v2, PDF p. 4, Unnumbered multipartite generalization: LOCC monotonicity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P10

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, paragraph on the prefactor and summary: multipartite LOCC
monotonicity with the chosen factor 1/2, retaining all n party labels while
allowing different positive local output dimensions. -/
theorem multipartite_locc_monotonicity {n : ℕ} (hn : 2 ≤ n)
    (s t : FiniteState n) (h : LOCC s [(1, t)]) :
    cemiFunctional t ≤ cemiFunctional s := by sorry

end QAlgorithms.Papers.Independent.Gap20.P10

end
