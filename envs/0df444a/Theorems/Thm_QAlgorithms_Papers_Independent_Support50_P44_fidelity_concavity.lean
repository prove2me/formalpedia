-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P44_fidelity_concavity
-- name    : QAlgorithms.Papers.Independent.Support50.P44.fidelity_concavity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T23:57:38.761676+00:00
-- url     : https://prove2.me/theorems/e6c08679-c567-4409-8129-9cb23a54c972
-- title:
--   Fidelity concavity and orthogonal-block equality
-- statement:
--   Let $\rho,\rho',\sigma,\sigma'$ be density operators on a complex separable Hilbert space, and let $p\in[0,1]$. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ for root fidelity. Then
--
--   $$F(p\rho+(1-p)\rho',p\sigma+(1-p)\sigma')\ge pF(\rho,\sigma)+(1-p)F(\rho',\sigma').$$
--
--   Equality holds when each of $\rho$ and $\sigma$ has support orthogonal to the support of each of $\rho'$ and $\sigma'$. This includes both endpoint probabilities and identifies the exact behavior of distinguishable blocks.
-- source:
--   Universal recovery map for approximate Markov chains, arXiv:1504.07251v3, PDF p. 23, Lemma A.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P44

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass compression)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Renew46.P37 (classicalKL)

open Filter

open scoped ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.23, Lemma A.1, (136): joint root-fidelity concavity and all four
cross-block conditions for equality. -/
theorem fidelity_concavity {I : Type*} [Countable I] (b : HilbertBasis I ℂ H)
    (rho rho2 sigma sigma2 : H →L[ℂ] H)
    (hrho : IsHilbertDensity b rho) (hrho2 : IsHilbertDensity b rho2)
    (hsigma : IsHilbertDensity b sigma) (hsigma2 : IsHilbertDensity b sigma2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * hilbertFidelity b rho sigma + (1-p) * hilbertFidelity b rho2 sigma2 ≤
      hilbertFidelity b (hilbertMix p rho rho2) (hilbertMix p sigma sigma2) ∧
    (OrthogonalBlocks rho rho2 sigma sigma2 →
      hilbertFidelity b (hilbertMix p rho rho2) (hilbertMix p sigma sigma2) =
        p * hilbertFidelity b rho sigma + (1-p) * hilbertFidelity b rho2 sigma2) := by sorry

end QAlgorithms.Papers.Independent.Support50.P44

end
