-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_signed_entropy_properties
-- name    : QAlgorithms.Papers.Independent.Next46.P23.signed_entropy_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:38:18.477925+00:00
-- url     : https://prove2.me/theorems/317ebcee-58bd-419d-80d0-b4bfdc78ef3b
-- title:
--   Proposition 2.17
-- statement:
--   Use signed relative entropy $S(\rho\mid\nu)$, natural logarithms and normalized states on nonzero finite-dimensional complex Hilbert spaces. It is nonpositive with equality exactly for equal states, equals $S(\rho)-\log\dim K$ against the chaotic state, and is unitarily invariant. For Gibbs states, $$S(\rho_A\mid\rho_B)=\log\frac{\operatorname{tr}e^A}{\operatorname{tr}e^B}-\rho_A(A-B),\quad S(\rho\mid\nu)=\lim_{\alpha\downarrow0}\frac{S_\alpha(\nu\mid\rho)}{\alpha}=\lim_{\alpha\uparrow1}\frac{S_\alpha(\rho\mid\nu)}{1-\alpha}.$$ With support inclusion the endpoint overlaps vanish and these limits are the corresponding derivatives, with a minus sign at one. Relative entropy increases under pullback by a unital Schwarz map, with states on its codomain. It is continuous when the second state is faithful and upper semicontinuous on all state pairs. Equal supports give $S_\alpha(\rho\mid\nu)\ge\alpha S(\nu\mid\rho)$ for every real $\alpha$. These are all eight clauses.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 48, Proposition 2.17

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Proposition2.17, all eight clauses, source PDF pp.48--49.
Clause6 uses codomain states, correcting the printed composition type error. -/
theorem signed_entropy_properties [Nonempty I] :
    (∀ rho nu : Mat I, QAlgorithms.IsDensityMatrix rho → QAlgorithms.IsDensityMatrix nu →
      signedRelativeEntropy rho nu ≤ 0 ∧ (signedRelativeEntropy rho nu = 0 ↔ rho = nu)) ∧
    (∀ rho : Mat I, QAlgorithms.IsDensityMatrix rho →
      signedRelativeEntropy rho (uniformDensity I) = ((entropy rho - Real.log (Fintype.card I) : ℝ) : EReal)) ∧
    (∀ rho nu : Mat I, QAlgorithms.IsDensityMatrix rho → QAlgorithms.IsDensityMatrix nu →
      ∀ U : Matrix.unitaryGroup I ℂ,
      signedRelativeEntropy ((U : Mat I) * rho * (U : Mat I)ᴴ)
        ((U : Mat I) * nu * (U : Mat I)ᴴ) = signedRelativeEntropy rho nu) ∧
    (∀ A B : Mat I, A.IsHermitian → B.IsHermitian →
      signedRelativeEntropy (QAlgorithms.gibbsState A) (QAlgorithms.gibbsState B) =
        ((Real.log ((NormedSpace.exp A).trace.re / (NormedSpace.exp B).trace.re) -
          ev (QAlgorithms.gibbsState A) (A-B) : ℝ) : EReal)) ∧
    (∀ rho nu : Mat I, QAlgorithms.IsDensityMatrix rho → QAlgorithms.IsDensityMatrix nu →
      Tendsto (fun a : ℝ => ((a⁻¹ : ℝ) : EReal) * renyi nu rho a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (signedRelativeEntropy rho nu)) ∧
      Tendsto (fun a : ℝ => (((1-a)⁻¹ : ℝ) : EReal) * renyi rho nu a)
        (nhdsWithin 1 (Set.Iio 1)) (nhds (signedRelativeEntropy rho nu)) ∧
      (Supports rho nu → renyi nu rho 0 = 0 ∧ renyi rho nu 1 = 0 ∧
        signedRelativeEntropy rho nu = ((deriv (renyiReal nu rho) (0 : ℝ) : ℝ) : EReal) ∧
        signedRelativeEntropy rho nu = ((-(deriv (renyiReal rho nu) (1 : ℝ)) : ℝ) : EReal))) ∧
    (∀ (K : Type) [Fintype K] [DecidableEq K] [Nonempty K],
      ∀ Phi : Mat I →ₗ[ℂ] Mat K, Phi 1 = 1 → Schwarz Phi →
      ∀ rho nu : Mat K, QAlgorithms.IsDensityMatrix rho → QAlgorithms.IsDensityMatrix nu →
        signedRelativeEntropy rho nu ≤ signedRelativeEntropy (pullback Phi rho) (pullback Phi nu)) ∧
    (ContinuousOn (fun p : Mat I × Mat I => signedRelativeEntropy p.1 p.2)
      {p | QAlgorithms.IsDensityMatrix p.1 ∧ QAlgorithms.IsDensityMatrix p.2 ∧ p.2.PosDef} ∧
      UpperSemicontinuousOn (fun p : Mat I × Mat I => signedRelativeEntropy p.1 p.2)
        {p | QAlgorithms.IsDensityMatrix p.1 ∧ QAlgorithms.IsDensityMatrix p.2}) ∧
    (∀ rho nu : Mat I, QAlgorithms.IsDensityMatrix rho → QAlgorithms.IsDensityMatrix nu →
      support rho = support nu → ∀ a : ℝ,
        (a : EReal) * signedRelativeEntropy nu rho ≤ renyi rho nu a) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
