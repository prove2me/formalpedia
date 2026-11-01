-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_quantumProfile
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.quantumProfile
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:16:18.886746+00:00
-- url     : https://prove2.me/theorems/4ee2ad83-621e-4468-ad39-b061254d38e5
-- title:
--   §5.3, quantum profile (44)–(45)
-- statement:
--   For density operators $\rho,\sigma$ and their chosen spectral-pair laws $p,q$, the quantum exponent satisfies
--
--   $$e_Q(r)=e_{p,q}(r)\quad(r\ge0).$$
--
--   If the pair is nonorthogonal, it has the complete conditional profile: $e_Q(r)=+\infty$ below $a=-\log\psi_1$, and $e_Q(r)=-\log\psi_0+\widetilde e(r-a)$ for $r\ge a$. At $a$ it equals $H(\widetilde q\|p)$; it is finite, convex and non-increasing thereafter, and is constant $-\log\psi_0$ for $r\ge H(\widetilde p\|q)$. Strictness is asserted only for distinct conditional laws. Supports are defined by actual positive probabilities.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 25, §5.3, quantum profile (44)–(45)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P45

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P45

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P07
  (support positivePart positiveProjection IsProjection)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (logNonnegativeExtended relativeEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P15 (positiveMatrixRpow)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:0708.4282v1, PDF pp.25,26,27: §5.3, quantum profile (44)–(45). Source corrections: PDF p.25 (45) repeats the reversed finite-branch inequality; use >= from Lemma 4 proof. Its support shorthand also omits zero overlap weights; use positive p and q. Independent moderation required. -/
theorem quantumProfile (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (D : SpectralPair rho sigma) :
    (∀ r : ℝ, 0 ≤ r → quantumExponent rho sigma r=
      classicalExponent (spectralP D) (spectralQ D) r) ∧
    (0 < overlapMass (spectralP D) (spectralQ D) →
     0 < overlapMass (spectralQ D) (spectralP D) →
      Profile (spectralP D) (spectralQ D) (quantumExponent rho sigma) ∧
      ∀ r : ℝ, 0 ≤ r → quantumExponent rho sigma r=
        if r < -Real.log (overlapMass (spectralQ D) (spectralP D)) then ⊤
        else (((-Real.log (overlapMass (spectralP D) (spectralQ D)) : ℝ) : EReal)+
          conditionalExponent (spectralP D) (spectralQ D)
            (r+Real.log (overlapMass (spectralQ D) (spectralP D))))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
