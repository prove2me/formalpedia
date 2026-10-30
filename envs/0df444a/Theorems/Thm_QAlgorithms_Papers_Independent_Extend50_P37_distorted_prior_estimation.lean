-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_distorted_prior_estimation
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.distorted_prior_estimation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:32:21.651078+00:00
-- url     : https://prove2.me/theorems/b1684629-f011-4718-8076-29997d48bec0
-- title:
--   Theorem 13: noiseless channels and gauge-distorted pure priors
-- statement:
--   Let $d,n\ge1$ and let the actual prior law on density matrices and its measurable parameter vector be invariant under $G_{\mathcal A}$. Let $\mathcal E$ be a physical channel noiseless on $\mathcal A^{\otimes n}$. Suppose the prior is the pushforward of a pure-state probability law by a physical single-copy channel $\mathcal N$ that is noiseless on $\mathcal A$ and satisfies $\mathcal N(U XU^*)=U\mathcal N(X)U^*$ for $U\in G_{\mathcal A}$. Then every arbitrary-outcome POVM $M$ admits a normalized local-algebra POVM $M'$ with
--   $$q_M(B\mid s\in\Delta)=q_{M'}(B\mid s\in\Delta).$$
--   Both sides refer to the original experiment $\mathcal E(\rho^{\otimes n})$, for every measurable $B$ and positive-probability parameter box $\Delta$. The pure preimage law need not initially be invariant, and $\mathcal E$ need not be covariant.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 20, Theorem 13: noiseless channels and gauge-distorted pure priors

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- PDF pp.20-21, Theorem 13: noiseless physical channels and covariant
noiseless distortions of pure priors. Covariance of E is not assumed. -/
theorem distorted_prior_estimation [Nonempty I] {O : Type*} [MeasurableSpace O]
    (n : ℕ) (hn : 0 < n) {l : ℕ} (A : StarSubalgebra ℂ (Mat I))
    (p : EstimationPrior I l) (hsym : Symmetry p (unitaryCentralizer (A : Set (Mat I))))
    (E : Mat (Fin n → I) → Mat (Fin n → I)) (hE : IsChannel E)
    (hquiet : Noiseless (tensorAlg n (A : Set (Mat I))) E)
    (N : Mat I → Mat I) (hdist : Distortion (A : Set (Mat I)) p N)
    (M : Measurements.OperatorPOVM (Fin n → I) O) :
    ∃ Mnew : Measurements.OperatorPOVM (Fin n → I) O,
      InAlgebra Mnew.operator (tensorAlg n (A : Set (Mat I))) ∧
      EquallyInformative p (E ∘ piKron n) M.operator Mnew.operator := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
