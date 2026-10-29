-- Prove2me | Theorems.Thm_PeskirShiryaev_General_sufficient_majorant
-- name    : PeskirShiryaev.General.sufficient_majorant
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:25:30.807923+00:00
-- url     : https://prove2.me/theorems/34efa250-aec5-4c7d-acb2-21f9bf05aa8a
-- title:
--   Theorem 2.7 — smallest-superharmonic-majorant criterion
-- statement:
--   Let $X$ satisfy the strong Markov and regularity assumptions of Section 2.2 on $E=\mathbb R^d$, $d\ge1$. Let $G:E\to\mathbb R$ be measurable with $E_x\sup_{t\ge0}|G(X_t)|<\infty$ for all $x$. Define $V(x)=\sup_\tau E_xG(X_\tau)$ over stopping times finite almost surely at the initial state. Suppose the smallest superharmonic majorant $\widehat V$ of $G$ exists, is lower semicontinuous, and $G$ is upper semicontinuous. Let
--   $$D=\{x:\widehat V(x)=G(x)\},\qquad \tau_D=\inf\{t\ge0:X_t\in D\}.$$
--   The entry time is a Markov time. If $P_x(\tau_D<\infty)=1$ for every $x$, then
--   $$\widehat V=V,\qquad E_xG(X_{\tau_D})=V(x)\quad(x\in E),$$
--   and $\tau_D$ is optimal. If $P_x(\tau_D<\infty)<1$ for some $x$, there is no almost-surely finite stopping rule optimal at every initial state.
--
--   This is the sufficient majorant criterion for existence, including its nonexistence alternative.
--
--   **Formalization Note** This item is the infinite-horizon Theorem 2.7 itself. The candidate majorant and the expected-reward value are separate objects, and equality is a conclusion. The nonexistence clause negates a common optimal rule for all initial states, matching the global convention of (2.2.9). Empty contact sets yield infinity. The finite-horizon extension in Remark 2.8 and Corollary 2.9 is outside this mission's scope.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 40–41 (PDF 60–61), Theorem 2.7, Eqs. (2.2.27)–(2.2.28); standing assumptions pp. 34–35.

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

theorem sufficient_majorant {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : MarkovModel d Ω) (G Vhat : State d → ℝ) (hG : GainIntegrable M G)
    (hmajorant : LeastMajorant M G Vhat)
    (hlsc : LowerSemicontinuous Vhat) (husc : UpperSemicontinuous G) :
    IsStoppingTime M.filtration (contactTime M G Vhat) ∧
    (((∀ x, ∀ᵐ ω ∂M.P x, contactTime M G Vhat ω < ⊤) →
      Vhat = value M G ∧ Optimal M G (contactTime M G Vhat)) ∧
    ((∃ x, M.P x {ω | contactTime M G Vhat ω < ⊤} < 1) →
      ¬ ∃ τ : Ω → ℝ≥0∞, Optimal M G τ)) := by sorry

end PeskirShiryaev.General
