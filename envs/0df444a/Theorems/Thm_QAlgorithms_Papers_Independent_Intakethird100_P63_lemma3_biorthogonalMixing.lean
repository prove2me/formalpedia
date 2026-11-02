-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P63_lemma3_biorthogonalMixing
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P63.lemma3_biorthogonalMixing
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:37:03.784444+00:00
-- url     : https://prove2.me/theorems/d1f0ce62-cff8-410a-8a9f-bd785d2c0839
-- title:
--   Lemma 3: biorthogonal mutual-information mixing
-- statement:
--   Let $(w_k,\rho^k)$ be a finite or countable ensemble of normalized positive trace-class bipartite states, written with nonnegative weights of sum one and arbitrary zero padding. Let $\rho=\sum_k w_k\rho^k$ be its computed mixture. Suppose its two marginal entropies are finite, and that for every distinct pair of positive-weight labels $k,l$, both $\rho_A^k\rho_A^l=0$ and $\rho_B^k\rho_B^l=0$. With natural logarithms, $H(w)=-\sum_k w_k\log w_k$ and $I(A:B)=S(\rho_A)+S(\rho_B)-S(\rho_{AB})$, one has
--
--   $$I(A:B)_\rho=H(w)+\sum_k w_k I(A:B)_{\rho^k}.$$
--
--   The formula is written using nonnegative extended sums; on this finite-entropy domain both terms on the right are finite. All reductions are actual partial traces. Active component entropy finiteness follows from finite mixture marginal entropies. Zero labels contribute zero and impose no component condition.
-- source:
--   On Mutual Information in Multipartite Quantum States and Equality in Strong Subadditivity of Entropy, arXiv:quant-ph/0311193v1, PDF p. 6, Lemma 3 (cited from Herbut [8], Lemma 9)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted nuclear trace-class, positive, trace-one predicate verbatim.

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

/-- Lemma 3, PDF p.6, cited there as Herbut [8], Lemma 9: biorthogonal
mutual-information mixing. The Shannon term uses the same natural logarithm as the
state entropy. Finite mixture subsystem entropies implement the source's entropy
cancellation domain and imply finite entropies of every positive-weight component. -/
theorem lemma3_biorthogonalMixing (e : DiscreteDensityEnsemble (Fin 2 → ℕ))
    (hbio : Biorthogonal e {0} {1})
    (hfinite : FiniteSubsystemEntropies (herbutMixture e)) :
    ENNReal.ofReal (clusterMutualInformation (herbutMixture e) {0} {1}) =
      QAlgorithms.Papers.Independent.Renew46.P08.countableShannonNats
        (fun k => ENNReal.ofReal (e.weight k)) +
      ∑' k, ENNReal.ofReal (e.weight k) *
        ENNReal.ofReal (clusterMutualInformation (e.component k) {0} {1}) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P63

end
