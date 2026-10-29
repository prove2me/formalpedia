-- Prove2me | Theorems.Thm_PeskirShiryaev_UltimateMaximum_optimal_prediction
-- name    : PeskirShiryaev.UltimateMaximum.optimal_prediction
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:56.310444+00:00
-- url     : https://prove2.me/theorems/0bb11ac8-1ccc-46ef-be99-d232a1cfa0c7
-- title:
--   Theorem 30.1 — optimal prediction of the Brownian maximum
-- statement:
--   Let $B$ be a standard real Brownian motion on a probability space, with measurable evaluations and continuous sample paths, and let $S_t=\sup_{0\le s\le t}B_s$. Let $\mathcal M$ consist of all stopping times for $\mathcal F_t^B=\sigma(B_s:0\le s\le t)$ taking values in $[0,1]$. There is a unique real root $z_*>0$ of
--   $$4\Phi(z_*)-2z_*\varphi(z_*)-3=0,$$
--   where $\Phi$ and $\varphi$ are the standard normal CDF and density. The time
--   $$\tau_*=\inf\{0\le t\le1:S_t-B_t\ge z_*\sqrt{1-t}\}$$
--   belongs to $\mathcal M$, its squared prediction error is integrable, and
--   $$\inf_{\tau\in\mathcal M}\mathbb E(B_\tau-S_1)^2=\mathbb E(B_{\tau_*}-S_1)^2=2\Phi(z_*)-1.$$
--   Thus the exact least mean-square error and an attaining stopping rule are both determined.
--
--   **Formalization Note** The infimum is a nonnegative extended-real infimum of nonnegative expectations. The attained expectation is also stated as a real integral with integrability, so no infinite or default-zero value is substituted. The process is indexed by nonnegative real time; only its unit-interval restriction enters the objective. The chosen Brownian version has continuous paths at every sample point. No independence from the future maximum is imposed, and the filtration is exactly the raw Brownian natural filtration.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 442 (PDF p. 458), Theorem 30.1, Eqs. (30.1.4)–(30.1.6)

import Mathlib
import Definitions.Def_PeskirShiryaev_UltimateMaximum_predictionModel

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeskirShiryaev.UltimateMaximum

theorem optimal_prediction {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (hmeas : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous (fun t => B t ω)) :
    0 < criticalLevel ∧ rootEquation criticalLevel = 0 ∧
    (∀ z : ℝ, rootEquation z = 0 → z = criticalLevel) ∧
    Admissible B (optimalTime B) ∧
    Integrable (squaredError B (optimalTime B)) P ∧
    (∫ ω, squaredError B (optimalTime B) ω ∂P) = 2 * Phi criticalLevel - 1 ∧
    predictionValue P B = ENNReal.ofReal (2 * Phi criticalLevel - 1) := by sorry

end PeskirShiryaev.UltimateMaximum

/- Imported definition bodies (verbatim code, for standalone inspection):

namespace PeskirShiryaev.UltimateMaximum

noncomputable def phi (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi)

noncomputable def Phi (x : ℝ) : ℝ := ∫ y in Iic x, phi y

noncomputable def runningCost (x : ℝ) : ℝ := 4 * Phi x - 3

noncomputable def rootEquation (z : ℝ) : ℝ := 4 * Phi z - 2 * z * phi z - 3

noncomputable def criticalLevel : ℝ := sInf {z : ℝ | 0 ≤ z ∧ rootEquation z = 0}

noncomputable def candidate (z : ℝ) : ℝ :=
  if |z| ≤ criticalLevel then
    Phi criticalLevel * (1 + z ^ 2) - |z| * phi |z| +
      (1 - z ^ 2) * Phi |z| - 3 / 2
  else 0

end PeskirShiryaev.UltimateMaximum

namespace PeskirShiryaev.UltimateMaximum

@[instance_reducible]
noncomputable def past {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ (s : ℝ≥0) (_ : s ≤ t), MeasurableSpace.comap (B s) inferInstance

def Admissible {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) : Prop :=
  (∀ t : ℝ≥0, MeasurableSet[past B t] {ω | τ ω ≤ t}) ∧ (∀ ω, τ ω ≤ 1)

noncomputable def maximum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  sSup {x : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ B s ω = x}

noncomputable def squaredError {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (ω : Ω) : ℝ := (B (τ ω) ω - maximum B 1 ω) ^ 2

noncomputable def predictionValue {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ⨅ τ : {τ : Ω → ℝ≥0 // Admissible B τ},
    ∫⁻ ω, ENNReal.ofReal (squaredError B τ.val ω) ∂P

noncomputable def optimalTime {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 :=
  sInf {t : ℝ≥0 | t ≤ 1 ∧
    maximum B t ω - B t ω ≥ criticalLevel * Real.sqrt (1 - (t : ℝ))}

noncomputable def clarkIntegrand {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  if t < 1 then 2 * (1 - Phi ((maximum B t ω - B t ω) / Real.sqrt (1 - (t : ℝ))))
  else 0

noncomputable def accumulatedCost {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (ω : Ω) : ℝ :=
  ∫ t in (0 : ℝ)..(τ ω : ℝ), 1 - 2 * clarkIntegrand B t.toNNReal ω

end PeskirShiryaev.UltimateMaximum
-/

/- Pinned Mathlib declaration bodies for the Brownian hypothesis (original namespaces:
ProbabilityTheory and ProbabilityTheory.BrownianReal for covMatrix/projectiveFamily):

structure IsBrownianReal (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop
    extends IsPreBrownianReal X P where
  cont : ∀ᵐ ω ∂P, Continuous (X · ω)

structure IsPreBrownianReal (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop where
  mk' ::
  hasLaw : ∀ I : Finset ℝ≥0, HasLaw (fun ω ↦ I.restrict (X · ω)) (projectiveFamily I) P

def covMatrix (I : Finset ℝ≥0) : Matrix I I ℝ := .of fun s t ↦ min s t

noncomputable def projectiveFamily (I : Finset ℝ≥0) : Measure (I → ℝ) :=
  multivariateGaussian 0 (covMatrix I) |>.map (MeasurableEquiv.toLp 2 (I → ℝ)).symm

/-- Multivariate Gaussian measure on `EuclideanSpace ℝ ι` with mean `μ` and covariance
matrix `S`. This only makes sense when `S` is positive semidefinite,
as then `CFC.sqrt S * CFC.sqrt S = S`. Otherwise `CFC.sqrt S = 0`, and
`multivariateGaussian μ S = Measure.dirac μ` (see `multivariateGaussian_of_not_posSemidef`). -/
noncomputable
def multivariateGaussian (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  (stdGaussian (EuclideanSpace ℝ ι)).map (fun x ↦ μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x)

variable (X μ) in
/-- The predicate `HasLaw X μ P` registers the fact that the random variable `X` has law `μ` under
the measure `P`, in other words that `P.map X = μ`. We also require `X` to be `AEMeasurable`,
to allow for nice interactions with operations on the codomain of `X`. See for instance
`HasLaw.comp`, `IndepFun.hasLaw_mul` and `IndepFun.hasLaw_add`. -/
@[fun_prop]
structure HasLaw (P : Measure Ω := by volume_tac) : Prop where
  protected aemeasurable : AEMeasurable X P := by fun_prop
  protected map_eq : P.map X = μ
-/
