-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_direct_sum_information
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.direct_sum_information
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:53:43.317648+00:00
-- url     : https://prove2.me/theorems/a46d9dd3-b1b7-4a0d-b2b2-5beeaa5dfbed
-- title:
--   Lemma 3: Holevo information of direct-sum mixtures
-- statement:
--   All quantum systems are nonzero finite-dimensional complex Hilbert spaces. States are positive semidefinite trace-one matrices, and channels are CPTP maps on the full matrix algebra. All entropies and logarithms are in bits. An ensemble is a finite probability distribution of states, with zero weights permitted. For a channel $\Phi$, write $\chi_\Phi(\rho)$ for the maximum ensemble Holevo information at mean $\rho$, $\widehat H_\Phi(\rho)$ for the minimum average output entropy at that mean, and $\overline C(\Phi;\mathcal A)$ for the maximum of $\chi_\Phi$ over a nonempty closed mean constraint $\mathcal A$.
--
--   Let $\{\Phi_j\}_{j\in T}$ be a nonempty finite family of channels with a common input and possibly different output spaces, and let $q_j\ge0$ with $\sum_jq_j=1$. Put $\Phi(X)=\bigoplus_jq_j\Phi_j(X)$. For every fixed input ensemble $e$,
--
--   $$\chi_\Phi(e)=\sum_{j\in T}q_j\chi_{\Phi_j}(e).$$
--
--   Here each ensemble chi is its output-mean entropy minus its average output entropy. This is an ensemble identity, allowing $q_j=0$, rather than an identity between independently optimized ensembles.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 8, Lemma 3: Holevo information of direct-sum mixtures

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P46

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Information100.P08
  (Ensemble ensembleAverage outputHolevo mixedRoof)

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- PDF p.8, Lemma 3: identity for a fixed ensemble, without separate branch
optimization. Branch output spaces may differ and weights may vanish. -/
theorem direct_sum_information [Nonempty I] {T : Type} [Fintype T] [DecidableEq T]
    [Nonempty T] {B : T → Type} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]
    [∀ t, Nonempty (B t)] (q : T → ℝ) (hq : ∀ t, 0 ≤ q t) (hsum : ∑ t, q t = 1)
    (Phi : (t : T) → Superop I (B t)) (hPhi : ∀ t, IsChannel (Phi t)) (e : Ensemble I) :
    outputHolevo (flaggedChannelSum q Phi) e = ∑ t, q t * outputHolevo (Phi t) e := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
