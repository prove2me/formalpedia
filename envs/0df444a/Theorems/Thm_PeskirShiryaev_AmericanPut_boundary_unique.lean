-- Prove2me | Theorems.Thm_PeskirShiryaev_AmericanPut_boundary_unique
-- name    : PeskirShiryaev.AmericanPut.boundary_unique
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:30.911237+00:00
-- url     : https://prove2.me/theorems/1bc1cfa3-2af5-4ed0-9094-773fe07aa412
-- title:
--   Theorem 25.3 — uniqueness of the American put boundary
-- statement:
--   Fix a geometric Brownian American put model with $r,\sigma,K,T>0$, and let $b$ be the boundary extracted from the optimal stopping value. Write $\gamma=r-\sigma^2/2$ and let $\Phi$ be the standard normal distribution function. The boundary $b$ is the unique continuous nondecreasing function $c:[0,T]\to\mathbb R$, satisfying $0<c(t)<K$ for $0<t<T$, which solves
--   $$K-c(t)=e^{-r(T-t)}\int_0^K\Phi\!\left(\frac{\log((K-z)/c(t))-\gamma(T-t)}{\sigma\sqrt{T-t}}\right)dz+rK\int_0^{T-t}e^{-ru}\Phi\!\left(\frac{\log(c(t+u)/c(t))-\gamma u}{\sigma\sqrt u}\right)du.$$
--   Both membership of $b$ in the candidate class and its satisfaction of the equation are conclusions; every other candidate solution coincides with $b$ throughout $[0,T]$.
--
--   This characterizes the optimal exercise boundary by a nonlinear Volterra integral equation.
--
--   **Formalization Note** The equation is interpreted with the transition-CDF endpoint conventions of the Kernels definition, including deterministic zero-time stock and the absorbing zero stock. Candidate endpoint values are not prescribed. Equality is on $[0,T]$, since Lean represents candidate functions as real functions. The value is an independently defined supremum of expected rewards, and the boundary is extracted from its stopping set; neither is defined by this equation.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 386 (PDF 402), Theorem 25.3 and Eq. (25.2.39); endpoint convention clarified by Remark 25.5, p. 392 (PDF 408)

import Definitions.Def_PeskirShiryaev_AmericanPut_Kernels

open scoped NNReal ENNReal

/- Imported dependency code, quoted verbatim for standalone inspection.

import Mathlib

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace PeskirShiryaev.AmericanPut

structure Model (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  probability : IsProbabilityMeasure P
  B : ℝ≥0 → Ω → ℝ
  measurable : ∀ s, StronglyMeasurable (B s)
  continuous : ∀ ω, Continuous (fun s => B s ω)
  brownian : IsBrownianReal B P
  r : ℝ
  sigma : ℝ
  K : ℝ
  T : ℝ
  r_pos : 0 < r
  sigma_pos : 0 < sigma
  K_pos : 0 < K
  T_pos : 0 < T

noncomputable def Model.filtration {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) :
    Filtration ℝ≥0 ‹MeasurableSpace Ω› :=
  Filtration.natural M.B M.measurable

noncomputable def Model.stock {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (x : ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  x * Real.exp (M.sigma * M.B s ω + (M.r - M.sigma ^ 2 / 2) * (s : ℝ))

def Model.payoff {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (x : ℝ) : ℝ :=
  max (M.K - x) 0

def Model.Admissible {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (t : ℝ) (τ : Ω → ℝ≥0) : Prop :=
  IsStoppingTime M.filtration (fun ω => (τ ω : WithTop ℝ≥0)) ∧
    ∀ ω, τ ω ≤ (M.T - t).toNNReal

noncomputable def Model.reward {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (x : ℝ) (τ : Ω → ℝ≥0) : ℝ :=
  ∫ ω, Real.exp (-M.r * (τ ω : ℝ)) * M.payoff (M.stock x (τ ω) ω) ∂M.P

noncomputable def Model.value {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (t x : ℝ) : ℝ :=
  sSup {v | ∃ τ : Ω → ℝ≥0, M.Admissible t τ ∧ v = M.reward x τ}

noncomputable def Model.modulus {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (δ : ℝ≥0) : ℝ :=
  ∫ ω, 1 - sInf ((fun s : ℝ≥0 => M.stock 1 s ω) '' Set.Icc 0 δ) ∂M.P

end PeskirShiryaev.AmericanPut

import Definitions.Def_PeskirShiryaev_AmericanPut_Model

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace PeskirShiryaev.AmericanPut

noncomputable def Model.boundary {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (t : ℝ) : ℝ :=
  sSup {x | x ∈ Set.Icc 0 M.K ∧ M.value t x = M.payoff x}

noncomputable def Model.hit {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (c : ℝ → ℝ) (t x : ℝ) (ω : Ω) : ℝ≥0 :=
  sInf (insert (M.T - t).toNNReal
    {s : ℝ≥0 | s ≤ (M.T - t).toNNReal ∧ M.stock x s ω ≤ c (t + (s : ℝ))})

def Model.Candidate {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (c : ℝ → ℝ) : Prop :=
  ContinuousOn c (Set.Icc 0 M.T) ∧ MonotoneOn c (Set.Icc 0 M.T) ∧
    ∀ t ∈ Set.Ioo 0 M.T, 0 < c t ∧ c t < M.K

end PeskirShiryaev.AmericanPut

import Definitions.Def_PeskirShiryaev_AmericanPut_Boundary

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace PeskirShiryaev.AmericanPut

noncomputable def normalCDF (a : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * ∫ z in Set.Iic a, Real.exp (-z ^ 2 / 2)

noncomputable def Model.transitionCDF {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (u x y : ℝ) : ℝ := by
  classical
  exact if u ≤ 0 then (if x ≤ y then 1 else 0)
    else if x = 0 then (if 0 ≤ y then 1 else 0)
    else if 0 < x then
      (if 0 < y then normalCDF ((Real.log (y / x) - (M.r - M.sigma ^ 2 / 2) * u) /
        (M.sigma * Real.sqrt u)) else 0)
    else (if y < 0 then 1 - normalCDF
      ((Real.log (y / x) - (M.r - M.sigma ^ 2 / 2) * u) / (M.sigma * Real.sqrt u))
      else 1)

noncomputable def Model.european {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (t x : ℝ) : ℝ :=
  Real.exp (-M.r * (M.T - t)) *
    (∫ z in (0 : ℝ)..M.K, M.transitionCDF (M.T - t) x (M.K - z))

noncomputable def Model.premium {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (c : ℝ → ℝ) (t x : ℝ) : ℝ :=
  M.r * M.K * (∫ u in (0 : ℝ)..(M.T - t),
    Real.exp (-M.r * u) * M.transitionCDF u x (c (t + u)))

def Model.Solves {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (c : ℝ → ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 M.T, M.K - c t = M.european t (c t) + M.premium c t (c t)

end PeskirShiryaev.AmericanPut

-/

namespace PeskirShiryaev.AmericanPut

theorem boundary_unique {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) :
    M.Candidate M.boundary ∧ M.Solves M.boundary ∧
    ∀ c : ℝ → ℝ, M.Candidate c → M.Solves c →
      Set.EqOn c M.boundary (Set.Icc 0 M.T) := by sorry

end PeskirShiryaev.AmericanPut
