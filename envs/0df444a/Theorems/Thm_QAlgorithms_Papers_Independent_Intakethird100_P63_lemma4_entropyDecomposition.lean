-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P63_lemma4_entropyDecomposition
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P63.lemma4_entropyDecomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:37:44.77292+00:00
-- url     : https://prove2.me/theorems/9de684d2-cfd3-463b-bac6-08f6578edb0f
-- title:
--   Lemma 4: entropy decomposition of an arbitrary discrete mixture
-- statement:
--   All states below are positive trace-class density operators of trace one on completed complex Hilbert tensor products, represented in countable orthonormal coordinates. Finite dimensional systems are included. Entropies use natural logarithms and the convention $0\log 0=0$. A discrete ensemble may have finitely or countably many components: its weights $w_k$ are nonnegative and sum to one, and each component with $w_k>0$ is a normalized density operator. Every mixture below is the computed trace-norm convergent sum $\rho=\sum_k w_k\rho^k$. All component conditions concern positive-weight labels only.
--
--   Assume only that the mixture has finite entropy, $S(\rho)<\infty$. Let $D(\sigma\|\rho)=\operatorname{Tr}(\sigma\log\sigma)-\operatorname{Tr}(\sigma\log\rho)$ denote Umegaki relative entropy, with value $+\infty$ on support failure. Then
--
--   $$S(\rho)=\sum_k w_k D(\rho^k\|\rho)+\sum_k w_k S(\rho^k).$$
--
--   Both sums are taken as nonnegative extended sums; their equality to the finite left side entails their finiteness. No orthogonality or Shannon-entropy bound is required. The component support inclusions follow from the mixture and are not assumptions.
-- source:
--   On Mutual Information in Multipartite Quantum States and Equality in Strong Subadditivity of Entropy, arXiv:quant-ph/0311193v1, PDF p. 6, Lemma 4: entropy decomposition of an arbitrary mixture by relative entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted nuclear trace-class, positive, trace-one predicate verbatim.

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

/-- Lemma 4, PDF p.6, (14b): entropy decomposition of any discrete mixture.
Only finite entropy of the computed mixture is assumed; no Shannon bound, support
inclusion premise, component entropy bounds, or orthogonality is added. -/
theorem lemma4_entropyDecomposition {I : Type} [Countable I] (e : DiscreteDensityEnsemble I)
    (hfinite : herbutEntropy (herbutMixture e) ≠ ⊤) :
    herbutEntropy (herbutMixture e) =
      (∑' k, ENNReal.ofReal (e.weight k) * traceClassDivergence (e.component k) (herbutMixture e)) +
      (∑' k, ENNReal.ofReal (e.weight k) * herbutEntropy (e.component k)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P63

end
