-- Prove2me | Theorems.Thm_PeskirShiryaev_General_necessary_majorant
-- name    : PeskirShiryaev.General.necessary_majorant
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:25:13.872454+00:00
-- url     : https://prove2.me/theorems/6bd0489e-ce71-4415-b021-5d36151f28af
-- title:
--   Theorem 2.4 — necessary superharmonic characterization and minimal optimal rule
-- statement:
--   Let $X$ be the strong Markov process of Section 2.2 on $E=\mathbb R^d$, $d\ge1$, and let the measurable gain $G$ satisfy $E_x\sup_{t\ge0}|G(X_t)|<\infty$ for every initial state. Define $V(x)=\sup_\tau E_xG(X_\tau)$ over almost-surely finite stopping times. Suppose that a single stopping rule $\tau_*$ is admissible and optimal at every initial state:
--   $$V(x)=E_xG(X_{\tau_*})\qquad(x\in E).$$
--   Then $V$ is the smallest superharmonic majorant of $G$. If in addition $V$ is lower semicontinuous and $G$ is upper semicontinuous, the first entry time $\tau_D$ of $D=\{V=G\}$ is optimal and
--   $$\tau_D\le\tau_*\quad P_x\text{-a.s.},\qquad (V(X_{t\wedge\tau_D}))_{t\ge0}\text{ is a right-continuous martingale under }P_x$$
--   for every $x\in E$.
--
--   The theorem supplies the necessity of the majorant characterization and the minimality of the contact rule when an optimal rule already exists.
--
--   **Formalization Note** Only the final optimal-contact and martingale conclusions require semicontinuity. The stopped process is explicitly integrable at every time, in addition to satisfying the martingale conditional-expectation identity. The infinity convention in the hitting time does not assert its finiteness in advance.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 37 (PDF 57), Theorem 2.4, Eqs. (2.2.9)–(2.2.12); standing assumptions pp. 34–35.

import Definitions.Def_PeskirShiryaev_General_StoppingProblem

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/- Imported Lean declarations, reproduced for self-contained code review:
namespace PeskirShiryaev.General

abbrev State (d : ℕ) := Fin d → ℝ


def RightContinuousPaths {Ω A : Type*} [TopologicalSpace A]
    (Y : ℝ≥0 → Ω → A) (ω : Ω) : Prop :=
  ∀ t, ContinuousWithinAt (fun s => Y s ω) (Ici t) t


structure MarkovModel (d : ℕ) (Ω : Type*) [mΩ : MeasurableSpace Ω] where
  dimension_pos : 0 < d
  P : State d → Measure Ω
  probability : ∀ x, IsProbabilityMeasure (P x)
  measurable_laws : ∀ A : Set Ω, MeasurableSet A → Measurable (fun x => P x A)
  filtration : Filtration ℝ≥0 mΩ
  filtration_rightContinuous : filtration.IsRightContinuous
  X : ℝ≥0 → Ω → State d
  adapted : Adapted filtration X
  starts : ∀ x, ∀ᵐ ω ∂P x, X 0 ω = x
  rightContinuous : ∀ ω, RightContinuousPaths X ω
  strongMarkov : ∀ (x : State d) (τ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime filtration τ),
    (∀ᵐ ω ∂P x, τ ω < ⊤) →
    ∀ (s : ℝ≥0) (f : State d → ℝ), Measurable f →
      Bornology.IsBounded (Set.range f) →
      (P x)[fun ω => f (X ((τ ω).toNNReal + s) ω) | hτ.measurableSpace]
        =ᵐ[P x] (fun ω => ∫ ω', f (X s ω') ∂P (X (τ ω).toNNReal ω))
  leftContinuous_stopping : ∀ (x : State d) (τ : Ω → ℝ≥0∞)
    (τn : ℕ → Ω → ℝ≥0∞),
    IsStoppingTime filtration τ →
    (∀ n, IsStoppingTime filtration (τn n)) →
    (∀ ω, Monotone (fun n => τn n ω)) →
    (∀ᵐ ω ∂P x, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) →
    ∀ᵐ ω ∂P x, τ ω < ⊤ →
      Tendsto (fun n => X (τn n ω).toNNReal ω) atTop (𝓝 (X (τ ω).toNNReal ω))

end PeskirShiryaev.General

namespace PeskirShiryaev.General

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]


def Admissible (M : MarkovModel d Ω) (x : State d) (τ : Ω → ℝ≥0∞) : Prop :=
  IsStoppingTime M.filtration τ ∧ ∀ᵐ ω ∂M.P x, τ ω < ⊤


noncomputable def gainSup (M : MarkovModel d Ω) (G : State d → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, ENNReal.ofReal |G (M.X t ω)|

def GainIntegrable (M : MarkovModel d Ω) (G : State d → ℝ) : Prop :=
  Measurable G ∧ ∀ x, AEMeasurable (gainSup M G) (M.P x) ∧
    (∫⁻ ω, gainSup M G ω ∂M.P x) < ⊤


noncomputable def reward (M : MarkovModel d Ω) (G : State d → ℝ)
    (τ : Ω → ℝ≥0∞) (ω : Ω) : ℝ :=
  if τ ω = ⊤ then 0 else G (M.X (τ ω).toNNReal ω)


noncomputable def value (M : MarkovModel d Ω) (G : State d → ℝ) (x : State d) : ℝ :=
  sSup {r : ℝ | ∃ τ : Ω → ℝ≥0∞, Admissible M x τ ∧ r = ∫ ω, reward M G τ ω ∂M.P x}

def Optimal (M : MarkovModel d Ω) (G : State d → ℝ) (τ : Ω → ℝ≥0∞) : Prop :=
  ∀ x, Admissible M x τ ∧ Integrable (reward M G τ) (M.P x) ∧
    (∫ ω, reward M G τ ω ∂M.P x) = value M G x


def Superharmonic (M : MarkovModel d Ω) (F : State d → ℝ) : Prop :=
  Measurable F ∧ ∀ (x : State d) (σ : Ω → ℝ≥0∞), Admissible M x σ →
    Integrable (reward M F σ) (M.P x) ∧ (∫ ω, reward M F σ ω ∂M.P x) ≤ F x

def LeastMajorant (M : MarkovModel d Ω) (G F : State d → ℝ) : Prop :=
  Superharmonic M F ∧ (∀ x, G x ≤ F x) ∧
    ∀ H : State d → ℝ, Superharmonic M H → (∀ x, G x ≤ H x) → ∀ x, F x ≤ H x


noncomputable def entryTime (M : MarkovModel d Ω) (D : Set (State d)) (ω : Ω) : ℝ≥0∞ :=
  ⨅ t : {t : ℝ≥0 // M.X t ω ∈ D}, (t.val : ℝ≥0∞)

noncomputable def contactTime (M : MarkovModel d Ω) (G F : State d → ℝ) : Ω → ℝ≥0∞ :=
  entryTime M {x | F x = G x}

noncomputable def stoppedValue (M : MarkovModel d Ω) (F : State d → ℝ)
    (τ : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : ℝ :=
  F (M.X (min (t : ℝ≥0∞) (τ ω)).toNNReal ω)

end PeskirShiryaev.General
-/

namespace PeskirShiryaev.General

theorem necessary_majorant {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : MarkovModel d Ω) (G : State d → ℝ) (hG : GainIntegrable M G)
    (τstar : Ω → ℝ≥0∞) (hopt : Optimal M G τstar) :
    LeastMajorant M G (value M G) ∧
    (LowerSemicontinuous (value M G) → UpperSemicontinuous G →
      Optimal M G (contactTime M G (value M G)) ∧
      ∀ x, (∀ᵐ ω ∂M.P x, contactTime M G (value M G) ω ≤ τstar ω) ∧
        (∀ t, Integrable (stoppedValue M (value M G) (contactTime M G (value M G)) t) (M.P x)) ∧
        Martingale (stoppedValue M (value M G) (contactTime M G (value M G))) M.filtration (M.P x) ∧
        ∀ᵐ ω ∂M.P x,
          RightContinuousPaths (stoppedValue M (value M G) (contactTime M G (value M G))) ω) := by sorry

end PeskirShiryaev.General
