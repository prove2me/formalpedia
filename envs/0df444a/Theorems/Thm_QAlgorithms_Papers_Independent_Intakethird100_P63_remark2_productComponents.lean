-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P63_remark2_productComponents
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P63.remark2_productComponents
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:39:38.978701+00:00
-- url     : https://prove2.me/theorems/cee07f37-8d6e-4622-9528-455d5b0b4dbb
-- title:
--   Remark 2: explicit SSA-equality mixtures of biorthogonal product components
-- statement:
--   All states below are positive trace-class density operators of trace one on completed complex Hilbert tensor products, represented in countable orthonormal coordinates. Finite dimensional systems are included. Entropies use natural logarithms and the convention $0\log 0=0$. Every subsystem entropy occurring in an entropy difference is finite; this is the proof-supported finite-entropy reading of the source, and imposes no finite Hilbert dimension.
--
--   Let $(w_k,\sigma_{12}^k)$ be a discrete ensemble of two-party states, with both marginal families orthogonal across distinct positive-weight labels. For every active label choose any normalized third-party density $\tau_3^k$. Set $\rho=\sum_k w_k(\sigma_{12}^k\otimes\tau_3^k)$, a trace-norm convergent sum. Then
--
--   $$I(1:2)_\rho=I(1:23)_\rho,$$
--
--   where $I(A:B)=S_A+S_B-S_{A\cup B}$. The third factors may coincide or differ. This constructs concrete members of the SSA-equality family.
-- source:
--   On Mutual Information in Multipartite Quantum States and Equality in Strong Subadditivity of Entropy, arXiv:quant-ph/0311193v1, PDF p. 7, Remark 2: concrete SSA-equality states from biorthogonal product components

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted nuclear trace-class, positive, trace-one predicate verbatim.

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

/-- Remark 2, PDF p.7: explicit SSA-equality states constructed from biorthogonal
two-party components and arbitrary third-party factors, which may coincide or differ. -/
theorem remark2_productComponents (e : DiscreteDensityEnsemble (Fin 2 → ℕ))
    (hbio : Biorthogonal e {0} {1}) (tau : ℕ → (Matrix ℕ ℕ ℂ))
    (htau : ∀ k, 0 < e.weight k → IsDensity (tau k))
    (hfinite : FiniteSubsystemEntropies (productMixture e tau)) :
    clusterMutualInformation (productMixture e tau) {0} {1} =
      clusterMutualInformation (productMixture e tau) {0} {1, 2} := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P63

end
