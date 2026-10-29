-- Prove2me | Theorems.Thm_PeskirShiryaev_UltimateMaximum_maximum_representation
-- name    : PeskirShiryaev.UltimateMaximum.maximum_representation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:49.346416+00:00
-- url     : https://prove2.me/theorems/20dcec81-09be-4735-85bf-ebdd4f813444
-- title:
--   Eqs. (30.1.7)–(30.1.8) — explicit maximum representation
-- statement:
--   Let $B$ be a standard real Brownian motion on a probability space $(\Omega,\mathcal F,P)$, with measurable evaluations and continuous sample paths. Write $S_t=\sup_{s\le t}B_s$, $\mathcal F_t^B=\sigma(B_s:s\le t)$, and $H_t=2[1-\Phi((S_t-B_t)/\sqrt{1-t})]$ for $t<1$, with $H_t=0$ for $t\ge1$.
--   Then $S_1\in L^2(P)$, $H_t$ is $\mathcal F_t^B$-measurable for every $t$, the pathwise integrals $\int_0^1 H_t^2\,dt$ exist for every sample point, and the random variable $\int_0^1H_t^2\,dt$ is integrable. The explicit integral representation is
--   $$S_1=\mathbb E S_1+\int_0^1H_t\,dB_t.$$
--   Here the centered maximum is the $L^2(P)$ limit of the left-endpoint dyadic stochastic sums. This is the representation of the future maximum by an adapted integrand used in the prediction problem.
--
--   **Formalization Note** The integral is encoded by the independently defined unit-interval $L^2$ limit relation. The statement includes square integrability of each approximating sum and its limit. It isolates the explicit representation in (30.1.7)–(30.1.8); the general Itô–Clark uniqueness theorem cited in the preceding prose is not separately posed. The processes are indexed by all nonnegative times but only $[0,1]$ enters the representation. Continuity is imposed on the chosen version at every sample point.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 442 (PDF p. 458), Eqs. (30.1.7)–(30.1.8)

import Mathlib
import Definitions.Def_PeskirShiryaev_UltimateMaximum_predictionModel
import Definitions.Def_PeskirShiryaev_UltimateMaximum_dyadicIntegral

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeskirShiryaev.UltimateMaximum

theorem maximum_representation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (hmeas : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous (fun t => B t ω)) :
    MemLp (maximum B 1) 2 P ∧
    (∀ t : ℝ≥0, Measurable[past B t] (clarkIntegrand B t)) ∧
    (∀ ω, IntervalIntegrable (fun t : ℝ => clarkIntegrand B t.toNNReal ω ^ 2)
      volume 0 1) ∧
    Integrable (fun ω => ∫ t in (0 : ℝ)..1, clarkIntegrand B t.toNNReal ω ^ 2) P ∧
    HasUnitDyadicIntegral P B (clarkIntegrand B)
      (fun ω => maximum B 1 ω - ∫ η, maximum B 1 η ∂P) := by sorry

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

namespace PeskirShiryaev.UltimateMaximum

noncomputable def dyadicSum {Ω : Type*} (B H : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), H ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) ω *
    (B (((k : ℝ≥0) + 1) / (2 : ℝ≥0) ^ n) ω - B ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) ω)

/-- Unit-horizon left-step L² integral relation. Its use below is for the explicit
bounded integrand, continuous on [0,1); it is not a definition for arbitrary predictable H. -/
def HasUnitDyadicIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B H : ℝ≥0 → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  MemLp X 2 P ∧ (∀ n, MemLp (dyadicSum B H n) 2 P) ∧
    Tendsto (fun n => eLpNorm (fun ω => dyadicSum B H n ω - X ω) 2 P)
      atTop (𝓝 0)

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
