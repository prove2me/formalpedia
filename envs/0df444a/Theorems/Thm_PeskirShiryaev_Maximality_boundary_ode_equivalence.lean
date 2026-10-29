-- Prove2me | Theorems.Thm_PeskirShiryaev_Maximality_boundary_ode_equivalence
-- name    : PeskirShiryaev.Maximality.boundary_ode_equivalence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:25:23.185024+00:00
-- url     : https://prove2.me/theorems/4e69a8ea-8354-423e-8196-0f35460ab062
-- title:
--   Eqs. (13.2.21)–(13.2.22) — The integral candidate solves the free-boundary system
-- statement:
--   Let $\rho,\sigma,c$ be continuous real coefficients, with $\sigma,c>0$, and let $g:\mathbb R\to\mathbb R$ be continuously differentiable with $g(s)<s$. Define $V_g(x,s)=s+\int_{g(s)}^x[L(x)-L(y)]c(y)m(dy)$. Then $V_g$ solves the generator equation $\rho(x)(V_g)_x+\tfrac12\sigma(x)^2(V_g)_{xx}=c(x)$ for $g(s)<x<s$, normal reflection at $x=s$, instantaneous stopping at $x=g(s)$, and smooth fit at $x=g(s)$, if and only if
--
--   $$g'(s)=\frac{\sigma(g(s))^2L'(g(s))}{2c(g(s))[L(s)-L(g(s))]}\quad\text{for every }s\in\mathbb R.$$
--
--   This identifies the ODE constraint on an analytic free boundary, independently of stochastic optimality.
--
--   **Formalization Note** Boundary derivatives are inward derivatives; the formula for $V_g$ has an analytic extension beyond the continuation region. The stochastic process is unnecessary for this deterministic equivalence.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 204–205 (PDF 223–224), Eqs. (13.2.9)–(13.2.12), paragraph following (13.2.21) and Eq. (13.2.22)

import Definitions.Def_PeskirShiryaev_Maximality_Boundary

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


-/

namespace PeskirShiryaev.Maximality

theorem boundary_ode_equivalence (p : Coefficients) (g : ℝ → ℝ)
    (hg : ContDiff ℝ 1 g) (hbelow : ∀ s, g s < s) :
    FreeBoundarySystem p g ↔ AdmissibleBoundary p g := by sorry

end PeskirShiryaev.Maximality
