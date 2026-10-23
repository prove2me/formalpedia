-- Prove2me | Theorems.Thm_RobustOpt2009_ScalarChance_proposition_2_3_1
-- name    : RobustOpt2009.ScalarChance.proposition_2_3_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:42:25.310985+00:00
-- url     : https://prove2.me/theorems/45fbb068-f2c3-4fa6-af01-bace608c2a96
-- title:
--   Proposition 2.3.1 — Tail bound for bounded mean-zero perturbations
-- statement:
--   Let $\zeta_1,\ldots,\zeta_L$ be independent measurable real random variables, each with mean zero and taking values in $[-1,1]$ almost surely. For every deterministic $z\in\mathbb R^L$ and $r\ge0$,
--   $$P\left\{\sum_i z_i\zeta_i>r\sqrt{\sum_i z_i^2}\right\}\le e^{-r^2/2}.$$
--   This is the bounded-perturbation tail estimate used in the chapter's basic safe approximations. Symmetry of the marginal distributions is not required.
--
--   **Formalization Note** The source's “taking values” is represented by almost-sure support, the usual probabilistic convention. Boundedness and measurability imply integrability of each mean. The event is strict, including when all weights vanish or $r=0$.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Proposition 2.3.1, (2.3.4), printed p. 32 (PDF p. 58).

import Definitions.Def_RobustOpt2009_ScalarChance_Setting

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/- Imported dependency source for blind auditing (verbatim):
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RobustOpt2009.ScalarChance

/-- Residual coordinates of (2.2.1); the nominal coordinate is stored separately. -/
noncomputable def residual {L n : ℕ} (a0 : Fin n → ℝ) (b0 : ℝ)
    (a : Fin L → Fin n → ℝ) (b : Fin L → ℝ) (x : Fin n → ℝ) :
    ℝ × (Fin L → ℝ) :=
  ((∑ j, a0 j * x j) - b0, fun i => (∑ j, a i j * x j) - b i)

/-- Robust feasibility of the affine residual for every perturbation in Z. -/
def RobustFeasible {L : ℕ} (Z : Set (Fin L → ℝ)) (z : ℝ × (Fin L → ℝ)) : Prop :=
  ∀ η ∈ Z, z.1 + ∑ i, η i * z.2 i ≤ 0

/-- Strict violation probability, (2.2.2) and (2.4.5). -/
noncomputable def violation {L : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Measure S) (ζ : Fin L → S → ℝ) (z : ℝ × (Fin L → ℝ)) : ℝ :=
  P.real {ω | 0 < z.1 + ∑ i, ζ i ω * z.2 i}

/-- P.2, including finite exponential expectations so the Bochner integral is genuine.
Parameter order and nonnegative sigma are separate theorem hypotheses. -/
def MGFMajorant {L : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Measure S) (ζ : Fin L → S → ℝ) (μminus μplus σ : Fin L → ℝ) : Prop :=
  ∀ (i : Fin L) (t : ℝ),
    Integrable (fun ω => Real.exp (t * ζ i ω)) P ∧
    (∫ ω, Real.exp (t * ζ i ω) ∂P) ≤
      Real.exp (max (μminus i * t) (μplus i * t) + (σ i)^2 * t^2 / 2)

/-- The deterministic box contribution in (2.4.8), for any lower and upper endpoints. -/
noncomputable def boxTerm {L : ℕ} (lo hi y : Fin L → ℝ) : ℝ :=
  ∑ i, max (lo i * y i) (hi i * y i)

/-- The weighted Euclidean term in (2.4.8). Zero sigma is permitted. -/
noncomputable def deviation {L : ℕ} (σ y : Fin L → ℝ) : ℝ :=
  Real.sqrt (∑ i, (σ i)^2 * (y i)^2)

/-- The radius in (2.4.10) and (2.4.13); used with 0 < ε < 1. -/
noncomputable def radius (ε : ℝ) : ℝ := Real.sqrt (2 * Real.log (1 / ε))

/-- The left side of the explicit convex constraint (2.4.8). -/
noncomputable def safeValue {L : ℕ} (μminus μplus σ : Fin L → ℝ) (ε : ℝ)
    (z : ℝ × (Fin L → ℝ)) : ℝ :=
  z.1 + boxTerm μminus μplus z.2 + radius ε * deviation σ z.2

/-- The moment uncertainty set (2.4.10). Writing the displacement as σ_i w_i
implements the printed extended-real convention for division by zero. -/
def momentSet {L : ℕ} (μminus μplus σ : Fin L → ℝ) (ε : ℝ) : Set (Fin L → ℝ) :=
  {η | ∃ w : Fin L → ℝ,
    (∀ i, μminus i ≤ η i - σ i * w i ∧ η i - σ i * w i ≤ μplus i) ∧
    Real.sqrt (∑ i, (w i)^2) ≤ radius ε}

/-- The intersection with the known support box, (2.4.13). -/
def boundedMomentSet {L : ℕ} (alo ahi μminus μplus σ : Fin L → ℝ) (ε : ℝ) :
    Set (Fin L → ℝ) :=
  {η | η ∈ momentSet μminus μplus σ ε ∧ ∀ i, alo i ≤ η i ∧ η i ≤ ahi i}

/-- The three constraints (2.4.14), including the nominal-coordinate split. -/
def SplitSystem {L : ℕ} (alo ahi μminus μplus σ : Fin L → ℝ) (ε : ℝ)
    (z u v : ℝ × (Fin L → ℝ)) : Prop :=
  z.1 = u.1 + v.1 ∧ (∀ i, z.2 i = u.2 i + v.2 i) ∧
  u.1 + boxTerm alo ahi u.2 ≤ 0 ∧ safeValue μminus μplus σ ε v ≤ 0

/-- Box intersected with a Euclidean ball, (2.3.9). -/
def boxBall {L : ℕ} (r : ℝ) : Set (Fin L → ℝ) :=
  {η | (∀ i, |η i| ≤ 1) ∧ Real.sqrt (∑ i, (η i)^2) ≤ r}

/-- The lifted conic system (2.3.10), with its printed negative residual sign. -/
def BoxBallSystem {L : ℕ} (r : ℝ) (z : ℝ × (Fin L → ℝ))
    (p q : Fin L → ℝ) : Prop :=
  (∀ i, p i + q i = -z.2 i) ∧
  (∑ i, |p i|) + r * Real.sqrt (∑ i, (q i)^2) ≤ -z.1

/-- The log-MGF upper bound Φ, (2.4.2). -/
noncomputable def phi {L : ℕ} (μminus μplus σ w : Fin L → ℝ) : ℝ :=
  ∑ i, (max (μminus i * w i) (μplus i * w i) + (σ i)^2 * (w i)^2 / 2)

/-- The exponential-certificate set Zε^o preceding (2.4.6), not a perturbation set. -/
def exponentialCertificateSet {L : ℕ} (μminus μplus σ : Fin L → ℝ) (ε : ℝ) :
    Set (ℝ × (Fin L → ℝ)) :=
  {z | ∃ α : ℝ, 0 < α ∧ α * z.1 + phi μminus μplus σ (fun i => α * z.2 i) ≤ Real.log ε}

/-- The closure Zε in (2.4.6), distinct from the uncertainty set in (2.4.10). -/
def closedCertificateSet {L : ℕ} (μminus μplus σ : Fin L → ℝ) (ε : ℝ) :
    Set (ℝ × (Fin L → ℝ)) :=
  closure (exponentialCertificateSet μminus μplus σ ε)

end RobustOpt2009.ScalarChance
-/

namespace RobustOpt2009.ScalarChance

theorem proposition_2_3_1 {L : ℕ} {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (ζ : Fin L → S → ℝ) (hmeas : ∀ i, Measurable (ζ i))
    (hindep : iIndepFun ζ P)
    (hmean : ∀ i, ∫ ω, ζ i ω ∂P = 0)
    (hbounded : ∀ i, ∀ᵐ ω ∂P, ζ i ω ∈ Set.Icc (-1 : ℝ) 1) (z : Fin L → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    P.real {ω | r * Real.sqrt (∑ i, (z i)^2) < ∑ i, z i * ζ i ω} ≤
      Real.exp (-(r^2 / 2)) := by sorry

end RobustOpt2009.ScalarChance
