-- Prove2me | Theorems.Thm_RobustOpt2009_MatrixChance_corollary_10_1_3
-- name    : RobustOpt2009.MatrixChance.corollary_10_1_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:44.289914+00:00
-- url     : https://prove2.me/theorems/64c06bb7-8f67-420d-b7cb-ede6ba4c9b98
-- title:
--   Corollary 10.1.3 — safe matrix chance constraints
-- statement:
--   Let $A,B_1,\ldots,B_L$ be deterministic real symmetric $m\times m$ matrices admitting matrices $Y_\ell$ with
--   $$\begin{pmatrix}Y_\ell&B_\ell\\B_\ell&A\end{pmatrix}\succeq0,\qquad \sum_\ell Y_\ell\preceq A.$$
--   Let $\Upsilon>0$ and $\chi>0$. Let $\zeta_1,\ldots,\zeta_L$ be independent measurable random variables satisfying either A.I (zero means and $|\zeta_\ell|\le1$ almost surely) or A.II (standard normal laws). Suppose
--   $$\Pr\left\{-\Upsilon A\preceq\sum_\ell\zeta_\ell B_\ell\preceq\Upsilon A\right\}\ge\chi.$$
--   1. Under A.I, for every $\Omega>\Upsilon$,
--   $$\Pr\left\{-\Omega A\preceq\sum_\ell\zeta_\ell B_\ell\preceq\Omega A\right\}\ge1-\chi^{-1}\exp\left(-\frac{(\Omega-\Upsilon)^2}{16}\right).$$
--   2. Under A.II and the additional condition $\chi>1/2$, for every $\Omega>\Upsilon$,
--   $$\Pr\left\{-\Omega A\preceq\sum_\ell\zeta_\ell B_\ell\preceq\Omega A\right\}\ge1-T\left(q(1-\chi)+(\Omega-\Upsilon)\max\{1,q(1-\chi)/\Upsilon\}\right).$$
--   This is the chapter goal: an explicit confidence amplification for a matrix inequality with a block-positive-semidefinite variance certificate. No positive-definiteness assumption is imposed on $A$; singular and zero $A$ remain permitted.
--
--   **Formalization Note** Matrices and perturbation coordinates have positive finite dimensions, indexed from zero in Lean. Probabilities are real values of probability measures. The function $T(t)=\Pr\{G>t\}$ for $G\sim N(0,1)$ is the book's upper-tail Erf, not the usual error function. Its quantile $q(p)=\inf\{t\in\overline{\mathbb R}:T(t)\le p\}$ is extended by $q(0)=+\infty$ and $q(1)=-\infty$; $T(+\infty)=0$ and $e^{-\infty^2/2}=0$. This makes the probability-one endpoint, not specified by (2.3.22), explicit without removing it. Finite arguments give exactly the displayed source formulas.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Corollary 10.1.3, printed pp. 240–241 (PDF pp. 266–267).

import Definitions.Def_RobustOpt2009_MatrixChance_Setting

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/- Verbatim dependency-source snapshot for the blind auditor.
The imported module remains authoritative.

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RobustOpt2009.MatrixChance

/-- Upper standard normal tail, extended to infinite thresholds by the event itself. -/
noncomputable def normalTail (t : EReal) : ℝ :=
  ((gaussianReal 0 1) {x : ℝ | t < (x : EReal)}).toReal

/-- The upper-tail quantile; at p=0 it is +∞, and at p=1 it is -∞. -/
noncomputable def tailQuantile (p : ℝ) : EReal :=
  sInf {t : EReal | normalTail t ≤ p}

/-- exp(-t²/2), with its limiting value zero at either infinite endpoint. -/
noncomputable def gaussianEnvelope (t : EReal) : ℝ :=
  if t = ⊤ ∨ t = ⊥ then 0 else Real.exp (-(t.toReal ^ 2) / 2)

/-- The Gaussian confidence-amplification argument in (10.1.12) and (10.1.16). -/
noncomputable def amplificationArgument (χ Υ Ω : ℝ) : EReal :=
  tailQuantile (1 - χ) + ((Ω - Υ : ℝ) : EReal) *
    max 1 (((Υ⁻¹ : ℝ) : EReal) * tailQuantile (1 - χ))

/-- Euclidean operator norm, not the entrywise or row-sum matrix norm. -/
noncomputable def spectralNorm {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖

/-- The linear matrix perturbation. -/
def perturbation {m L : ℕ} (B : Fin L → Matrix (Fin m) (Fin m) ℝ)
    (z : Fin L → ℝ) : Matrix (Fin m) (Fin m) ℝ := ∑ l, z l • B l

/-- The two Loewner inequalities -t A ≤ S ≤ t A. -/
def sandwich {m : ℕ} (A S : Matrix (Fin m) (Fin m) ℝ) (t : ℝ) : Prop :=
  (S + t • A).PosSemidef ∧ (t • A - S).PosSemidef

/-- Block positive-semidefinite certificate (10.1.13). -/
def varianceCertificate {m L : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (B : Fin L → Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∃ Y : Fin L → Matrix (Fin m) (Fin m) ℝ,
    (∀ l, (Matrix.fromBlocks (Y l) (B l) (B l) A).PosSemidef) ∧
      (A - ∑ l, Y l).PosSemidef

/-- A.I, with the zero mean stipulated at the start of Section 10.1. -/
def boundedCase {W : Type*} [MeasurableSpace W] {L : ℕ}
    (μ : Measure W) (ζ : Fin L → W → ℝ) : Prop :=
  ∀ l, (∀ᵐ w ∂μ, |ζ l w| ≤ 1) ∧ (∫ w, ζ l w ∂μ) = 0

/-- A.II: every coordinate has the standard normal law. Measurability is a theorem premise. -/
def gaussianCase {W : Type*} [MeasurableSpace W] {L : ℕ}
    (μ : Measure W) (ζ : Fin L → W → ℝ) : Prop :=
  ∀ l, μ.map (ζ l) = gaussianReal 0 1

end RobustOpt2009.MatrixChance

End dependency-source snapshot. -/

namespace RobustOpt2009.MatrixChance

theorem corollary_10_1_3 {W : Type*} [MeasurableSpace W]
    (μ : Measure W) [IsProbabilityMeasure μ] {m L : ℕ} [NeZero m] [NeZero L]
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Fin L → Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsSymm) (hB : ∀ l, (B l).IsSymm)
    (hcertificate : varianceCertificate A B)
    (ζ : Fin L → W → ℝ) (hmeas : ∀ l, Measurable (ζ l))
    (hindep : iIndepFun ζ μ) (hcase : boundedCase μ ζ ∨ gaussianCase μ ζ)
    (Υ χ : ℝ) (hΥ : 0 < Υ) (hχ : 0 < χ)
    (hbase : χ ≤ (μ {w | sandwich A (perturbation B (fun l => ζ l w)) Υ}).toReal) :
    (boundedCase μ ζ → ∀ Ω : ℝ, Υ < Ω →
      1 - (1 / χ) * Real.exp (-((Ω - Υ) ^ 2) / 16) ≤
        (μ {w | sandwich A (perturbation B (fun l => ζ l w)) Ω}).toReal) ∧
    (gaussianCase μ ζ → (1 / 2 : ℝ) < χ → ∀ Ω : ℝ, Υ < Ω →
      1 - normalTail (amplificationArgument χ Υ Ω) ≤
        (μ {w | sandwich A (perturbation B (fun l => ζ l w)) Ω}).toReal) := by sorry

end RobustOpt2009.MatrixChance
