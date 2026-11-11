-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_master_theorem
-- name    : QuantumFunctionalEstimation.Master.master_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:29:58.179912+00:00
-- url     : https://prove2.me/theorems/d531b976-c000-4e5e-a3e6-f911503050a8
-- title:
--   Theorem 4.2 — master theorem for quantum functional estimation
-- statement:
--   There are universal real constants $C\ge4$, $0<c\le1/1536$, with $2048c/225\le1/16$, and a universal integer threshold $d_0\ge2$. For every $d\ge d_0$, let $\mu_0,\mu_1$ be arbitrary Borel probability laws matching moments zero through $K$, supported on $I=[a,b]\subseteq[0,\infty)$ and having common mean $\nu\le1$. Let $\phi:[0,\infty)\to\mathbb R$ have finite positive $A_\phi,L_\phi,g_\phi$ as in Definition 4.1. The function is a.e. measurable under both input laws. Suppose
--   $$K\ge C\log d,\qquad (1+M)^2\le\frac{cd}{\log d},\qquad\frac{A_\phi+(b-a)L_\phi}{g_\phi}\le c\sqrt d.$$
--   There exist state priors $P_0,P_1$, equal to the Definition 3.3 laws with $q=\lfloor d/4\rfloor$, and nonempty real intervals $I_0,I_1$ such that
--   $$\operatorname{dist}(I_0,I_1)\ge g_\phi/8,$$
--   $$T\left(\int\rho^{\otimes n}\,dP_0,\int\rho^{\otimes n}\,dP_1\right)\le d^{-2}\quad\left(1\le n\le n_0=\left\lfloor\frac{cd^2}{M^2}\right\rfloor\right),$$
--   $$P_b\{\rho:\mathcal L_\phi(\rho)\in I_b\}\ge0.99\quad(b=0,1).$$
--   Both further conclusions hold for these same priors:
--
--   1. Every collective estimator successful with probability at least $2/3$ on every state at error $g_\phi/24$ uses $n>n_0$ copies, hence requires $\Omega(d^2/M^2)$ copies.
--   2. For every $0<p\le1$, positive integer $d'$, fixed $d'$-dimensional state $\sigma$, arbitrary real functional $\Phi$ on $(d+d')$-dimensional states, error $\varepsilon\ge0$, and nonempty intervals $J_0,J_1$ with $\operatorname{dist}(J_0,J_1)>2\varepsilon$, if
--   $$P_b\{\rho:\Phi(p\rho\oplus(1-p)\sigma)\in J_b\}\ge0.99\quad(b=0,1),$$
--   then every collective estimator of $\Phi$ successful on every state with probability at least $2/3$ at error $\varepsilon$ uses
--   $$n>\left\lfloor\frac{n_0}{10p}\right\rfloor,$$
--   and therefore requires $\Omega(d^2/(pM^2))$ copies. All events appearing in probabilities are measurable in the completed respective priors.
--
--   The theorem gives a single functional criterion for hard quantum estimation instances. It includes arbitrary state rank, every sufficiently large integer dimension, arbitrary Borel input laws, and all collective POVMs.
--
--   **Formalization Note** The explicit decay, constant restrictions, and exclusions are supported by the proof on printed pp. 19–20 (PDF pp. 21–22). No constant or threshold depends on the laws, dimension, functional, auxiliary state, mixing probability, or estimator. Finite oscillation together with law-relative measurability ensures integrability of $\phi$; no global continuity or boundedness is assumed.
--
--   Differences from the source:
--   - generalization: unspecified inverse polynomial decay and Omega sample rates → d^-2 decay, C>=4, c<=1/1536, 2048c/225<=1/16, and exclusions n>n0 and n>floor(n0/(10p)); reason: Eq. (20) and the two testing arguments on printed pp. 19–20 give these explicit uniform bounds and imply both printed rates
--   - generalization: existence of hard priors → priors equal the Definition 3.3 construction with q=floor(d/4); reason: the proof on printed p. 18 constructs exactly these priors, so forgetting the equalities recovers the full source conclusion
--   - encoding: phi defined on the nonnegative half-line with finite positive parameters → a real extension, a spectral sum, boundedness of the oscillation and slope sets, and their positive real suprema; reason: state eigenvalues and supported scalar inputs use only nonnegative arguments; boundedness excludes default values for unbounded suprema
--   - encoding: expectations and probability events are implicitly measurable → law-relative AEStronglyMeasurable phi and completed-prior NullMeasurableSet events; reason: states the source probability convention without global regularity or any finite-support restriction
--   - encoding: all collective estimators on n copies of dimensions d and d+d′ → published OperatorPOVM/copyLaw with registers Fin n → Fin d and Fin n → (Fin d ⊕ Fin d′); reason: real outcomes include measurable post-processing, and the sum register has exactly dimension d+d′
--   - encoding: nonempty real intervals and their distance → nonempty order-connected sets and the infimum of pairwise absolute differences; reason: preserves arbitrary endpoint conventions and unbounded intervals while keeping the infimum nonempty and bounded below
--   - generalization: "for sufficiently large d" stated after the instance is fixed, with the probabilities in (18) presupposing measurable events → one universal threshold d_0 chosen with C and c before all data, and null-measurability of the two events in (18) asserted as a conclusion; reason: every threshold in the proof on printed pp. 18–20 depends only on C, c and d (q=floor(d/4)>=d/6, b0<=d/12, the d^-2 and 0.99 estimates), and the events are null-measurable because phi is Lipschitz on [1/2,4/3] where the residual eigenvalue lies; forgetting both recovers the source
--   - encoding: error epsilon and auxiliary dimension d′ unrestricted → 0<=epsilon and 0<d′; reason: for epsilon<0 the target interval is empty so no estimator succeeds, and no d′=0 state exists, so only vacuous instances are excluded
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), Theorem 4.2 and Definition 4.1, printed p. 18 (PDF p. 20); proof printed pp. 19–20 (PDF pp. 21–22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/451.pdf

import Definitions.Def_QuantumFunctionalEstimation_Master_Encodings
import Definitions.Def_QuantumFunctionalEstimation_Master_Functionals
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal BigOperators Matrix ComplexOrder Matrix.Norms.Elementwise

namespace QuantumFunctionalEstimation.Master

/-- Entire Theorem 4.2, printed p.18 (PDF p.20), with the proof-supported d^-2 decay
and copy exclusions n<=n0 and n<=floor(n0/(10p)). All constants are universal.
Only law-relative a.e. measurability of phi and of the probability events is required. -/
theorem master_theorem :
    ∃ (C c : ℝ) (d₀ : ℕ), 4 ≤ C ∧ 0 < c ∧ c ≤ 1 / 1536 ∧
      2048 * c / 225 ≤ 1 / 16 ∧ 2 ≤ d₀ ∧
    ∀ (d K : ℕ), d₀ ≤ d →
    ∀ (a b ν : ℝ) (μ₀ μ₁ : ProbabilityMeasure ℝ) (φ : ℝ → ℝ),
      0 ≤ a → a ≤ b → MomentMatching K μ₀ μ₁ →
      Supported μ₀ (Set.Icc a b) → Supported μ₁ (Set.Icc a b) →
      (∫ x, x ∂(μ₀ : Measure ℝ)) = ν →
      (∫ x, x ∂(μ₁ : Measure ℝ)) = ν → ν ≤ 1 →
      AEStronglyMeasurable φ (μ₀ : Measure ℝ) →
      AEStronglyMeasurable φ (μ₁ : Measure ℝ) →
      BddAbove (oscillationValues φ a b) → BddAbove (slopeValues φ) →
      0 < oscillation φ a b → 0 < localLipschitz φ → 0 < gap φ μ₀ μ₁ →
      C * Real.log d ≤ K →
      (1 + radius a b) ^ 2 ≤ c * d / Real.log d →
      (oscillation φ a b + (b - a) * localLipschitz φ) / gap φ μ₀ μ₁ ≤ c * Real.sqrt d →
      ∃ (P₀ P₁ : ProbabilityMeasure (State d)) (I₀ I₁ : RealInterval),
        (P₀ : Measure (State d)) = multiPrior d (d / 4) μ₀ ∧
        (P₁ : Measure (State d)) = multiPrior d (d / 4) μ₁ ∧
        gap φ μ₀ μ₁ / 8 ≤ intervalDistance I₀ I₁ ∧
        (∀ n : ℕ, 1 ≤ n → n ≤ copyCutoff c d a b →
          QAlgorithms.traceDistance (averageCopies (P₀ : Measure (State d)) n)
            (averageCopies (P₁ : Measure (State d)) n) ≤ (d : ℝ)⁻¹ ^ 2) ∧
        NullMeasurableSet {ρ : State d | spectralFunctional φ ρ.val ∈ I₀.carrier}
          (P₀ : Measure (State d)) ∧
        NullMeasurableSet {ρ : State d | spectralFunctional φ ρ.val ∈ I₁.carrier}
          (P₁ : Measure (State d)) ∧
        (99 / 100 : ℝ≥0∞) ≤ (P₀ : Measure (State d))
          {ρ | spectralFunctional φ ρ.val ∈ I₀.carrier} ∧
        (99 / 100 : ℝ≥0∞) ≤ (P₁ : Measure (State d))
          {ρ | spectralFunctional φ ρ.val ∈ I₁.carrier} ∧
        (∀ (n : ℕ) (E : QAlgorithms.Measurements.OperatorPOVM (Fin n → Fin d) ℝ),
          Successful (spectralFunctional φ) (gap φ μ₀ μ₁ / 24) n E →
          copyCutoff c d a b < n) ∧
        (∀ (p : ℝ), 0 < p → p ≤ 1 → ∀ (d' : ℕ), 0 < d' →
          ∀ (σ : Matrix (Fin d') (Fin d') ℂ), QAlgorithms.IsDensityMatrix σ →
          ∀ (Φ : Matrix (Fin d ⊕ Fin d') (Fin d ⊕ Fin d') ℂ → ℝ)
            (ε : ℝ) (J₀ J₁ : RealInterval), 0 ≤ ε →
            2 * ε < intervalDistance J₀ J₁ →
            NullMeasurableSet {ρ : State d | Φ (directSum p ρ.val σ) ∈ J₀.carrier}
              (P₀ : Measure (State d)) →
            NullMeasurableSet {ρ : State d | Φ (directSum p ρ.val σ) ∈ J₁.carrier}
              (P₁ : Measure (State d)) →
            (99 / 100 : ℝ≥0∞) ≤ (P₀ : Measure (State d))
              {ρ | Φ (directSum p ρ.val σ) ∈ J₀.carrier} →
            (99 / 100 : ℝ≥0∞) ≤ (P₁ : Measure (State d))
              {ρ | Φ (directSum p ρ.val σ) ∈ J₁.carrier} →
            ∀ (n : ℕ) (E : QAlgorithms.Measurements.OperatorPOVM
              (Fin n → (Fin d ⊕ Fin d')) ℝ),
              Successful Φ ε n E → ⌊(copyCutoff c d a b : ℝ) / (10 * p)⌋₊ < n) := by sorry

end QuantumFunctionalEstimation.Master
