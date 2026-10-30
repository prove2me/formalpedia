-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P38_weakMonotonicityUnderDephasing
-- name    : QAlgorithms.Papers.Independent.Bridge50.P38.weakMonotonicityUnderDephasing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:39:11.718442+00:00
-- url     : https://prove2.me/theorems/c339f482-d78f-41e8-a320-46347ab1254a
-- title:
--   Weak collision monotonicity under dephasing
-- statement:
--   Let $A$ and its reference $R$ have dimension $d\ge1$, let $B$ be a nonempty finite-dimensional complex system, and let $\Lambda:A\to B$ be a completely positive linear map. Let $T_U$ and $Z_U$ be the dephasing and one-based clock associated with a unitary $U$ on $R$. Suppose $\sigma_{RB}$ is a density matrix satisfying $(\Gamma_{Z_U}\otimes\operatorname{id}_B)(\sigma)=\sigma$, where $\Gamma_Z(X)=ZXZ^\dagger$. Define $C_2(X\|S)=\operatorname{tr}(XS^{-1/2}XS^{-1/2})$, with inverses on the support. Then
--
--   $$C_2((T_U\otimes\Lambda)(\Phi_d)\|\sigma)\ge\frac1d C_2((\operatorname{id}_R\otimes\Lambda)(\Phi_d)\|\sigma).$$
--
--   Only $\sigma$ is required to be normalized; neither trace preservation of $\Lambda$ nor normalization of its output is imposed. The collision quadratic form expresses the source's collision exponential while retaining the zero-map case.
-- source:
--   Decoding quantum information via the Petz recovery map, arXiv:1504.04449v4, PDF p. 10, lemma-3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P38

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Bridge50.P38

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

open QAlgorithms.Papers.Independent.Information100.P63 (normalQuantile)

open QAlgorithms.Papers.Independent.Dependency50.P36
  (relativeEntropyFinite pairInformationVariance)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (columnProjector pinch marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification singleUseInformation coherentInformation)

open QAlgorithms.Papers.Independent.Gap48.P23 (CompletelyPositive)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- PDF pp.10–11, Lemma 3.4: weak monotonicity for a CP map, including
non-trace-preserving and zero maps; sigma alone is a normalized state. -/
theorem weakMonotonicityUnderDephasing {d : ℕ} [NeZero d] [Nonempty B]
    (L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hL : CompletelyPositive (L : Superop (Fin d) B))
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (sigma : Matrix (Fin d × B) (Fin d × B) ℂ) (hsigma : IsDensityMatrix sigma)
    (hinvariant : firstAction (conjSuperop (basisClock U)) sigma = sigma) :
    (1 / (d : ℝ)) * collisionExponential
      (idTensorSuperop L (pureDensity (finiteMaxEntangled (Fin d)))) sigma ≤
    collisionExponential
      (firstAction (pinch (U : Matrix (Fin d) (Fin d) ℂ)) (idTensorSuperop L
        (pureDensity (finiteMaxEntangled (Fin d))))) sigma := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P38

end
