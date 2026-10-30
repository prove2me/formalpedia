-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P40_entropy_fidelity_bound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P40.entropy_fidelity_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:05:39.55925+00:00
-- url     : https://prove2.me/theorems/61b10f77-e13a-4972-b295-a9fd8b515584
-- title:
--   Rényi entropy and root fidelity (van Dam and Hayden)
-- statement:
--   All registers are finite and nonempty, all source kets have unit norm, all density operators are positive semidefinite with trace one, logarithms are base two, and F denotes root fidelity. For density operators $\rho,\sigma$ on the same register, $0\le F\le F(\rho,\sigma)$ and $1/2\le a<1$, put $b=\infty$ when $a=1/2$ and $b=a/(2a-1)$ otherwise. Then
--
--   $$F\le 2^{\frac{1-a}{2a}[S_a(\rho)-S_b(\sigma)]}.$$
--
--   $S_a$ is state Rényi entropy in bits and $S_\infty(\sigma)=-\log_2\lambda_{\max}(\sigma)$. This is the exponentiated form of (23), including zero fidelity.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, PDF p. 6, Lemma 5, equation (23)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P40

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply marginalAR)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (cq)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6, Lemma 5 (van Dam and Hayden [22]), (23): root fidelity,
including a=1/2 with infinite conjugate order. Exponentiation includes F=0. -/
theorem entropy_fidelity_bound {I : Type} [Fintype I] [Nonempty I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (hsigma : IsDensityMatrix sigma) (F a : ℝ)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (hF : F ≤ rootFidelity rho sigma)
    (ha : (1 : ℝ) / 2 ≤ a) (ha1 : a < 1) :
    F ≤ (2 : ℝ) ^ ((1 - a) / (2 * a) *
      (renyiEntropy a rho -
        if a = (1 : ℝ) / 2 then entropyInfinity sigma
        else renyiEntropy (a / (2 * a - 1)) sigma)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P40

end
