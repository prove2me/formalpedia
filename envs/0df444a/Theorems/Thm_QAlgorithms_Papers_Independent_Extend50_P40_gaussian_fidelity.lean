-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_gaussian_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.gaussian_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:15:41.696478+00:00
-- url     : https://prove2.me/theorems/55ac8448-fd45-4f28-8576-a22fcd46b6c7
-- title:
--   §III.A Eqs.(53)–(56): coherent-state marginal fidelity
-- statement:
--   On the complete oscillator space, let $\rho_t(\alpha)$ be the normalized coherent-state mixture with density $e^{-|\beta|^2/t}/(\pi t)$ against complex-plane Lebesgue measure, with $\rho_0(\alpha)=|\alpha\rangle\langle\alpha|$. For $t\ge0$ this is a positive trace-one trace-class operator, the positive-t operator integral exists, and
--
--   $$
--   \langle\alpha|\rho_t(\alpha)|\alpha\rangle=\frac1{1+t}.
--   $$
--
--   At t=1/N−1/M with 1≤N<M this gives MN/(MN+M−N). Coherent vectors are normalized and the t=0 boundary does not use a singular Gaussian integral.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 15, §III.A Eqs.(53)–(56): coherent-state marginal fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P40

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open MeasureTheory Filter

open scoped Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)

open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeHilbert ModeOperator IsModeDensity FockWeylSystem)

open QAlgorithms.Papers.Independent.Renew46.P41
  (coherentProduct NormalizedCoherent IsReducedDensity FockCanonicalAction
   ModeUnitary twoModeAmplifierQuadratures modeMixingQuadratures embeddedOpticalBeam
   displacedThermal cloneNoise cloneFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentProjector)

/-- III.A, PDF p.15 Eqs.(53)–(56): normalization, convergence and pure-target
fidelity of the full-space Gaussian marginal, including zero added noise. -/
theorem gaussian_fidelity (t : ℝ) (ht : 0 ≤ t) (alpha : ℂ) :
    NormalizedCoherent (fun _ : Fin 1 => alpha) ∧ IsModeDensity (gaussianMixture t alpha) ∧
    (t > 0 → Integrable (fun beta : ℂ =>
      (noiseWeight t beta : ℂ) • oneModeProjector (alpha + beta)) volume) ∧
    (inner ℂ (coherentProduct (fun _ : Fin 1 => alpha))
      (gaussianMixture t alpha (coherentProduct (fun _ : Fin 1 => alpha)))).re = 1 / (1 + t) ∧
    (∀ N M : ℕ, 1 ≤ N → N < M →
      1 / (1 + (1 / (N : ℝ) - 1 / (M : ℝ))) = cloneFidelity N M) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
