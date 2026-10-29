-- Prove2me | Theorems.Thm_PeskirShiryaev_Maximality_maximality_principle
-- name    : PeskirShiryaev.Maximality.maximality_principle
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:22.12735+00:00
-- url     : https://prove2.me/theorems/31f3ed58-8dd1-4cf2-8858-818372427b83
-- title:
--   Theorem 13.2 — Optimal stopping of the maximum process
-- statement:
--   Let $X$ be a nonexplosive real diffusion with continuous drift $\rho$, continuous strictly positive volatility $\sigma$, and continuous strictly positive cost $c$. Start from $X_0=x\le s=S_0$ and optimize over almost surely finite stopping times of $X$ with finite expected accumulated cost.
--
--   For every maximal globally admissible solution $g_*$ of the boundary ODE, the source asserts that the value is finite and
--
--   $$V_*(x,s)=\begin{cases}s+\displaystyle\int_{g_*(s)}^x[L(x)-L(y)]c(y)m(dy),&g_*(s)\le x\le s,\\s,&x\le g_*(s).\end{cases}$$
--
--   The rule $\tau_*=\inf\{t>0:X_t\le g_*(S_t)\}$ is a stopping time. It is optimal when its expected cost is finite. Otherwise, diagonal-contact ODE solutions $g_n\downarrow g_*$ have admissible hitting times $\tau_{g_n}\uparrow\tau_*$ whose expected rewards converge to $V_*(x,s)$, as in (13.2.41). If any admissible optimal rule $\tau$ exists, then $\tau_*\le\tau$ almost surely and $\tau_*$ is optimal as well.
--
--   If there is no maximal admissible ODE solution, the source asserts
--
--   $$V_*(x,s)=+\infty\quad\text{and there is no optimal stopping time.}$$
--
--   This is the source's full finite/infinite alternative and maximality characterization, retained as the mission goal.
--
--   **Formalization Note** The value is independently defined as an extended-real supremum, and maximality is pointwise comparison among global ODE solutions. Almost sure finiteness follows the book's Definition 2.1. No finite-reward restriction is added to admissibility or optimality. Under this literal interpretation, the final nonattainment clause has the counterexample recorded in FINDINGS.yaml F4; the faithful source statement is retained rather than silently corrected.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 207 (PDF 226), Theorem 13.2, with approximation Eq. (13.2.41) on p. 210 (PDF 229) and monotone hitting-time statement on p. 213 (PDF 232)

import Definitions.Def_PeskirShiryaev_Maximality_Stopping

open MeasureTheory
open scoped ENNReal NNReal

/- Imported declaration context (verbatim, for a self-contained blind code audit):

structure Coefficients where
  drift : ℝ → ℝ
  volatility : ℝ → ℝ
  cost : ℝ → ℝ
  drift_continuous : Continuous drift
  volatility_continuous : Continuous volatility
  volatility_pos : ∀ x, 0 < volatility x
  cost_continuous : Continuous cost
  cost_pos : ∀ x, 0 < cost x

noncomputable def itoSum {Ω : Type*} (σ : ℝ → ℝ)
    (X B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n),
    σ (X (t * (k : ℝ≥0) / (2 ^ n : ℝ≥0)) ω) *
      (B (t * ((k + 1 : ℕ) : ℝ≥0) / (2 ^ n : ℝ≥0)) ω -
       B (t * (k : ℝ≥0) / (2 ^ n : ℝ≥0)) ω)

/-- A nonexplosive weak solution on R. The stochastic integral is specified by
its defining left dyadic sums in probability, not by an unconstrained integral oracle. -/
structure Diffusion {Ω : Type*} [MeasurableSpace Ω] (p : Coefficients)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (x : ℝ) : Prop where
  probability : IsProbabilityMeasure P
  measurable : ∀ t, Measurable (X t)
  continuous : ∀ ω, Continuous (fun t => X t ω)
  initial : ∀ᵐ ω ∂P, X 0 ω = x
  weak_solution : ∃ (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (B : ℝ≥0 → Ω → ℝ),
    Adapted ℱ X ∧ Adapted ℱ B ∧ IsBrownianReal B P ∧
    (∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (ℱ s) P) ∧
    ∀ t : ℝ≥0, TendstoInMeasure P (itoSum p.volatility X B t) atTop
      (fun ω => X t ω - x -
        ∫ r in (0 : ℝ)..(t : ℝ), p.drift (X r.toNNReal ω))

/-- Right-continuous natural past, augmented by ambient measurable null sets. -/
noncomputable def naturalPast {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : MeasurableSpace Ω :=
  ⨅ u : ℝ≥0, ⨅ (_ : t < u),
    ((⨆ r : ℝ≥0, ⨆ (_ : r ≤ u), MeasurableSpace.comap (X r) inferInstance) ⊔
      MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet N ∧ P N = 0})

/-- The book's Markov times; a stopping time must additionally be finite a.s. -/
def IsMarkovTime {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞) : Prop :=
  Measurable τ ∧ ∀ t : ℝ≥0, MeasurableSet[naturalPast P X t] {ω | τ ω ≤ (t : ℝ≥0∞)}



noncomputable def scaleDensity (p : Coefficients) (y : ℝ) : ℝ :=
  Real.exp (- ∫ z in (0 : ℝ)..y, 2 * p.drift z / p.volatility z ^ 2)

noncomputable def scale (p : Coefficients) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..x, scaleDensity p y

noncomputable def speedDensity (p : Coefficients) (x : ℝ) : ℝ :=
  2 / (scaleDensity p x * p.volatility x ^ 2)

noncomputable def speed (p : Coefficients) : Measure ℝ :=
  volume.withDensity (fun y => ENNReal.ofReal (speedDensity p y))

noncomputable def green (p : Coefficients) (a b x y : ℝ) : ℝ :=
  if y ≤ x then (scale p b - scale p x) * (scale p y - scale p a) /
      (scale p b - scale p a)
  else (scale p b - scale p y) * (scale p x - scale p a) /
      (scale p b - scale p a)

noncomputable def odeRhs (p : Coefficients) (s y : ℝ) : ℝ :=
  p.volatility y ^ 2 * scaleDensity p y /
    (2 * p.cost y * (scale p s - scale p y))

/-- Global C1 solutions strictly below the diagonal; no optimality is assumed. -/
def AdmissibleBoundary (p : Coefficients) (g : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 g ∧ ∀ s, g s < s ∧ HasDerivAt g (odeRhs p s (g s)) s

def MaximalBoundary (p : Coefficients) (g : ℝ → ℝ) : Prop :=
  AdmissibleBoundary p g ∧ ∀ h, AdmissibleBoundary p h → ∀ s, h s ≤ g s

/-- The analytic expression, extended to either side of its lower integration limit. -/
noncomputable def integralCandidate (p : Coefficients) (g : ℝ → ℝ) (x s : ℝ) : ℝ :=
  s + ∫ y in g s..x, (scale p x - scale p y) * p.cost y * speedDensity p y

noncomputable def candidate (p : Coefficients) (g : ℝ → ℝ) (x s : ℝ) : ℝ :=
  if x ≤ g s then s else integralCandidate p g x s

/-- Equations (13.2.9)--(13.2.12), with inward derivatives at the two boundaries. -/
def FreeBoundarySystem (p : Coefficients) (g : ℝ → ℝ) : Prop :=
  (∀ s x, g s < x → x < s →
    p.drift x * deriv (fun z => integralCandidate p g z s) x +
    p.volatility x ^ 2 / 2 * deriv (deriv (fun z => integralCandidate p g z s)) x =
      p.cost x) ∧
  (∀ s, HasDerivWithinAt (fun u => integralCandidate p g s u) 0 (Set.Ici s) s) ∧
  (∀ s, integralCandidate p g (g s) s = s) ∧
  (∀ s, HasDerivWithinAt (fun x => integralCandidate p g x s) 0 (Set.Ici (g s)) (g s))

/-- A solution up to its first diagonal contact, extended by the diagonal afterwards. -/
def DiagonalBoundary (p : Coefficients) (g : ℝ → ℝ) (d : ℝ) : Prop :=
  Continuous g ∧
  (∀ s, s < d → g s < s ∧ HasDerivAt g (odeRhs p s (g s)) s) ∧
  ∀ s, d ≤ s → g s = s



noncomputable def runningMaximum {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (s : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  max s (sSup ((fun r => X r ω) '' Set.Icc 0 t))

noncomputable def accumulatedCost {Ω : Type*} (p : Coefficients)
    (X : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ r : ℝ in {r : ℝ | 0 ≤ r ∧ ENNReal.ofReal r < τ ω},
    ENNReal.ofReal (p.cost (X r.toNNReal ω))

noncomputable def expectedCost {Ω : Type*} [MeasurableSpace Ω] (p : Coefficients)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, accumulatedCost p X τ ω ∂P

def AdmissibleTime {Ω : Type*} [MeasurableSpace Ω] (p : Coefficients)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞) : Prop :=
  IsMarkovTime P X τ ∧ (∀ᵐ ω ∂P, τ ω < ⊤) ∧ expectedCost p P X τ < ⊤

/-- The lower bound S_tau >= s makes the positive-increment representation exact.
The subtraction is only used for admissible times, whose expected cost is finite. -/
noncomputable def reward {Ω : Type*} [MeasurableSpace Ω] (p : Coefficients)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (τ : Ω → ℝ≥0∞) : EReal :=
  (s : EReal) + (∫⁻ ω, ENNReal.ofReal (runningMaximum X s (τ ω).toNNReal ω - s) ∂P).toEReal -
    (expectedCost p P X τ).toEReal

noncomputable def value {Ω : Type*} [MeasurableSpace Ω] (p : Coefficients)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (s : ℝ) : EReal :=
  ⨆ τ : Ω → ℝ≥0∞, ⨆ (_ : AdmissibleTime p P X τ), reward p P X s τ

def OptimalTime {Ω : Type*} [MeasurableSpace Ω] (p : Coefficients)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (τ : Ω → ℝ≥0∞) : Prop :=
  AdmissibleTime p P X τ ∧ reward p P X s τ = value p P X s

noncomputable def boundaryTime {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (s : ℝ) (g : ℝ → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ t : ℝ≥0, ⨅ (_ : 0 < t ∧ X t ω ≤ g (runningMaximum X s t ω)), (t : ℝ≥0∞)

noncomputable def candidateReward {Ω : Type*} [MeasurableSpace Ω] (p : Coefficients)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (g : ℝ → ℝ)
    (τ : Ω → ℝ≥0∞) : EReal :=
  (s : EReal) + (∫⁻ ω, ENNReal.ofReal
    (candidate p g (X (τ ω).toNNReal ω) (runningMaximum X s (τ ω).toNNReal ω) - s) ∂P).toEReal -
    (expectedCost p P X τ).toEReal

/-- The boundary approximation specified in (13.2.41) and the subsequent discussion. -/
def BoundaryApproximation {Ω : Type*} [MeasurableSpace Ω] (p : Coefficients)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (g : ℝ → ℝ) : Prop :=
  ∃ (gn : ℕ → ℝ → ℝ) (dn : ℕ → ℝ),
    (∀ n, DiagonalBoundary p (gn n) (dn n)) ∧
    (∀ u, Antitone (fun n => gn n u) ∧ Tendsto (fun n => gn n u) atTop (𝓝 (g u))) ∧
    (∀ n, AdmissibleTime p P X (boundaryTime X s (gn n))) ∧
    (∀ᵐ ω ∂P, Monotone (fun n => boundaryTime X s (gn n) ω) ∧
      Tendsto (fun n => boundaryTime X s (gn n) ω) atTop (𝓝 (boundaryTime X s g ω))) ∧
    Tendsto (fun n => reward p P X s (boundaryTime X s (gn n))) atTop (𝓝 (value p P X s))


-/

namespace PeskirShiryaev.Maximality

theorem maximality_principle {Ω : Type*} [MeasurableSpace Ω]
    (p : Coefficients) (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (x s : ℝ)
    (hX : Diffusion p P X x) (hxs : x ≤ s) :
    (∀ g : ℝ → ℝ, MaximalBoundary p g →
      value p P X s = (candidate p g x s : EReal) ∧
      IsMarkovTime P X (boundaryTime X s g) ∧
      (∀ᵐ ω ∂P, boundaryTime X s g ω < ⊤) ∧
      (expectedCost p P X (boundaryTime X s g) < ⊤ →
        OptimalTime p P X s (boundaryTime X s g)) ∧
      (expectedCost p P X (boundaryTime X s g) = ⊤ → BoundaryApproximation p P X s g) ∧
      (∀ τ : Ω → ℝ≥0∞, OptimalTime p P X s τ →
        (∀ᵐ ω ∂P, boundaryTime X s g ω ≤ τ ω) ∧
        OptimalTime p P X s (boundaryTime X s g))) ∧
    ((¬ ∃ g : ℝ → ℝ, MaximalBoundary p g) →
      value p P X s = ⊤ ∧ ¬ ∃ τ : Ω → ℝ≥0∞, OptimalTime p P X s τ) := by sorry

end PeskirShiryaev.Maximality
