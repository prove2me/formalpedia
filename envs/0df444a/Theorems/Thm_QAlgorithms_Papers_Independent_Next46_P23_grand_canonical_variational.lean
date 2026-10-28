-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_grand_canonical_variational
-- name    : QAlgorithms.Papers.Independent.Next46.P23.grand_canonical_variational
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:43:12.718841+00:00
-- url     : https://prove2.me/theorems/2eeb951a-f256-4119-9185-746c335792d0
-- title:
--   §2.9: grand-canonical Gibbs variational principle
-- statement:
--   Let self-adjoint $H,N$ commute on a nonzero finite-dimensional complex Hilbert space, and let $\beta,\mu\in\mathbb R$. Set $\rho_{\beta,\mu}=e^{-\beta(H-\mu N)}/\operatorname{tr}e^{-\beta(H-\mu N)}$, $E=\rho_{\beta,\mu}(H)$, $q=\rho_{\beta,\mu}(N)$ and $P=\log\operatorname{tr}e^{-\beta(H-\mu N)}$. Then $$S(\rho_{\beta,\mu})=\beta(E-\mu q)+P.$$ This state uniquely maximizes entropy subject to these two expectations and satisfies the $\beta$-KMS identity for the physical dynamics on observables commuting with $N$. Wherever a differentiable local inverse $(E,q)\mapsto(\beta,\mu)$ exists, $\partial_ES=\beta$ and $\partial_qS=-\beta\mu$. No inverse parameterization is assumed to exist globally.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 54, §2.9: grand-canonical Gibbs variational principle

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

/-- Grand-canonical Gibbs variational principle, source PDF pp.54--55.
Means are constructed from beta,mu; inverse-parameter derivatives are conditional on
an actual differentiable local inverse, as required by the source's parameterization. -/
theorem grand_canonical_variational [Nonempty I] (H N : Mat I) (hH : H.IsHermitian)
    (hN : N.IsHermitian) (hcomm : H*N = N*H) (beta mu : ℝ) :
    let rhoG := QAlgorithms.gibbsState ((-(beta : ℂ)) • (H - (mu : ℂ) • N))
    entropy rhoG = beta * (ev rhoG H - mu * ev rhoG N) +
      Real.log ((NormedSpace.exp ((-(beta : ℂ)) • (H - (mu : ℂ) • N))).trace.re) ∧
    QAlgorithms.IsDensityMatrix rhoG ∧
    (∀ rho : Mat I, QAlgorithms.IsDensityMatrix rho →
      ev rho H = ev rhoG H → ev rho N = ev rhoG N →
        entropy rho ≤ entropy rhoG ∧ (entropy rho = entropy rhoG ↔ rho = rhoG)) ∧
    (∀ A B : Mat I, A*N = N*A → B*N = N*B →
      (rhoG * (complexTau H (-Complex.I * (beta : ℂ)) B * A)).trace = (rhoG * (A*B)).trace) ∧
    (∀ b m : ℝ × ℝ → ℝ, ∀ x : ℝ × ℝ,
      DifferentiableAt ℝ b x → DifferentiableAt ℝ m x →
      (∀ᶠ y in nhds x,
        let rhoY := QAlgorithms.gibbsState ((-(b y : ℂ)) • (H - (m y : ℂ) • N))
        ev rhoY H = y.1 ∧ ev rhoY N = y.2) →
      let S : ℝ × ℝ → ℝ := fun y => entropy
        (QAlgorithms.gibbsState ((-(b y : ℂ)) • (H - (m y : ℂ) • N)))
      fderiv ℝ S x (1,0) = b x ∧ fderiv ℝ S x (0,1) = -b x * m x) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
