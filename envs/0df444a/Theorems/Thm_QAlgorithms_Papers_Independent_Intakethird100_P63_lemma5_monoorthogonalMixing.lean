-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P63_lemma5_monoorthogonalMixing
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P63.lemma5_monoorthogonalMixing
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:38:57.190659+00:00
-- url     : https://prove2.me/theorems/ffed478b-febc-4415-98b3-c4dd44f78c81
-- title:
--   Lemma 5: mutual-information mixing for a monoorthogonal decomposition
-- statement:
--   All states below are positive trace-class density operators of trace one on completed complex Hilbert tensor products, represented in countable orthonormal coordinates. Finite dimensional systems are included. Entropies use natural logarithms and the convention $0\log 0=0$. Every subsystem entropy occurring in an entropy difference is finite; this is the proof-supported finite-entropy reading of the source, and imposes no finite Hilbert dimension. A discrete ensemble may have finitely or countably many components: its weights $w_k$ are nonnegative and sum to one, and each component with $w_k>0$ is a normalized density operator. Every mixture below is the computed trace-norm convergent sum $\rho=\sum_k w_k\rho^k$. All component conditions concern positive-weight labels only.
--
--   Consider a bipartite ensemble on parties $2,3$, monoorthogonal on party $2$: $\rho_2^k\rho_2^l=0$ for distinct active labels. Let $D$ be Umegaki relative entropy and let $I(2:3)=S_2+S_3-S_{23}$. Then
--
--   $$I(2:3)_\rho=\sum_k w_k D(\rho_3^k\|\rho_3)+\sum_k w_k I(2:3)_{\rho^k}.$$
--
--   The sums may first be formed as nonnegative extended sums and are finite on this domain. This describes information in a mixture with orthogonality on only one subsystem; neither SSA equality nor third-party orthogonality is required.
-- source:
--   On Mutual Information in Multipartite Quantum States and Equality in Strong Subadditivity of Entropy, arXiv:quant-ph/0311193v1, PDF p. 7, Lemma 5: mutual-information mixing for a monoorthogonal decomposition

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted nuclear trace-class, positive, trace-one predicate verbatim.

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

/-- Lemma 5, PDF p.7, (18): monoorthogonal mutual-information mixing. The relative
entropy uses third-party marginals, with two plus signs and no Shannon term. -/
theorem lemma5_monoorthogonalMixing (e : DiscreteDensityEnsemble (Fin 2 → ℕ))
    (hmono : Monoorthogonal e {0})
    (hfinite : FiniteSubsystemEntropies (herbutMixture e)) :
    ENNReal.ofReal (clusterMutualInformation (herbutMixture e) {0} {1}) =
      (∑' k, ENNReal.ofReal (e.weight k) *
        traceClassDivergence (herbutReduction (e.component k) {1}) (herbutReduction (herbutMixture e) {1})) +
      (∑' k, ENNReal.ofReal (e.weight k) *
        ENNReal.ofReal (clusterMutualInformation (e.component k) {0} {1})) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P63

end
