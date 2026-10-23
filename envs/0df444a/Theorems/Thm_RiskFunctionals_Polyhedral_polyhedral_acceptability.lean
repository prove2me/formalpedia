-- Prove2me | Theorems.Thm_RiskFunctionals_Polyhedral_polyhedral_acceptability
-- name    : RiskFunctionals.Polyhedral.polyhedral_acceptability
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:54:46.066887+00:00
-- url     : https://prove2.me/theorems/8674eaab-2892-4792-bc63-e71db2008451
-- title:
--   Theorem 3.39 — when a polyhedral functional is a multi-period acceptability functional
-- statement:
--   In the setting of Definition 3.37 ($T\ge1$, a filtration with trivial $\mathcal F_0$, $p\in[1,\infty)$, $1/p+1/q=1$, non-empty polyhedral $V_t$), let $\mathcal A$ be the polyhedral functional (3.54), let complete recourse (i) hold, and let $\mathcal Z_*$ be the dual set (3.56).
--
--   (a) If $\mathcal Z_*\subseteq\{Z\in\mathcal Z:Z_t\ge0,\ \mathbb E(Z_t\mid\mathcal F_{t-1})=1,\ t=1,\dots,T\}$ (3.60), then $\mathcal A$ satisfies (MA0)–(MA3) (a multi-period acceptability functional).
--
--   (b) If $\mathcal Z_*\subseteq\{Z\in\mathcal Z:Z_t\ge0,\ \mathbb E(Z_t)=1,\ t=1,\dots,T\}$ (3.61), then $\mathcal A$ satisfies (MA0), (MA1′), (MA2), (MA3).
--
--   In both cases $\mathcal A$ is strict (MA5): $\mathcal A(Y)\le\sum_{t=1}^T\mathbb E(Y_t)$.
--
--   (c) If, in addition, dual feasibility (ii) holds and $\mathcal Z_*\subseteq\{Z\in\mathcal Z:Z_t\ge0,\ \mathbb E(Z_1)=1\}$ (3.62), then $\mathcal A$ satisfies (MA0), (MA1″), (MA2), (MA3).
--
--   In all cases $\mathcal A$ is finite, continuous and positively homogeneous (MA4).
--
--   These three inclusions are the book's recipe for designing polyhedral functionals with a prescribed form of translation equivariance.
--
--   **Formalization Note** Each case is an implication whose conclusion lists finiteness on $\mathcal Y$ and every property the theorem attributes to that case, including continuity and (MA4). Finiteness implies properness, which Definition 3.14 includes in "multi-period acceptability functional". The properties (MA1)–(MA5) are stated for the real part of $\mathcal A$; (MA0) compares `EReal` values over pairs of filtrations. "$Z_t\ge0$" is almost sure; $\mathbb E(Z_t\mid\mathcal F_{t-1})=1$ is almost sure. Parts (a) and (b) are stated exactly as printed, with complete recourse (i) as the only standing condition; finding F1 shows they fail when $\mathcal Z_*=\emptyset$, and the `_corrected` variant adds $\mathcal Z_*\neq\emptyset$.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 163, Theorem 3.39

import Mathlib
import Definitions.Def_RiskFunctionals_Polyhedral_Cones
import Definitions.Def_RiskFunctionals_Polyhedral_MultiPeriod

namespace RiskFunctionals.Polyhedral

open MeasureTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 163,
Theorem 3.39. Let `𝒜` be the polyhedral functional (3.54) and let complete recourse (i) hold.
(a) If `𝒵* ⊆ {Z ∈ 𝒵 : Z_t ≥ 0, 𝔼(Z_t | ℱ_{t−1}) = 1, t = 1, …, T}` (3.60), `𝒜` is a
multi-period acceptability functional ((MA0)–(MA3)). (b) If
`𝒵* ⊆ {Z ∈ 𝒵 : Z_t ≥ 0, 𝔼(Z_t) = 1, t = 1, …, T}` (3.61), `𝒜` satisfies (MA0), (MA1′),
(MA2), (MA3). In both cases `𝒜` is strict (MA5). (c) If in addition dual feasibility (ii)
holds and `𝒵* ⊆ {Z ∈ 𝒵 : Z_t ≥ 0, 𝔼(Z₁) = 1}` (3.62), `𝒜` satisfies (MA0), (MA1″), (MA2),
(MA3). In all cases `𝒜` is finite, continuous and positively homogeneous (MA4).
Stated as printed: parts (a) and (b) assume only (i); see the `_corrected` variant. -/
theorem polyhedral_acceptability {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ = 1) (T : ℕ) (hT : 1 ≤ T) (𝓕 : ℕ → MeasurableSpace Ω)
    (h𝓕 : IsFiltrationUpTo mΩ T 𝓕) (D : MultiPeriodData) (hD : D.IsPolyhedral T)
    (hi : D.CompleteRecourse T) :
    (D.dualSet P q T 𝓕 ⊆ {Z : ℕ → Ω → ℝ | ∀ t ∈ Finset.Icc 1 T,
        (∀ᵐ ω ∂P, 0 ≤ Z t ω) ∧ ∀ᵐ ω ∂P, P[Z t | 𝓕 (t - 1)] ω = 1} →
      (∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y →
        D.functional P p T 𝓕 Y ≠ ⊥ ∧ D.functional P p T 𝓕 Y ≠ ⊤) ∧
      InformationMonotone P p T (fun 𝓖 Y => D.functional P p T 𝓖 Y) ∧
      PredictableTranslationEquivariant P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      ConcaveOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      MonotoneOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      StrictOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      ContinuousOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      PositivelyHomogeneousOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal)) ∧
    (D.dualSet P q T 𝓕 ⊆ {Z : ℕ → Ω → ℝ | ∀ t ∈ Finset.Icc 1 T,
        (∀ᵐ ω ∂P, 0 ≤ Z t ω) ∧ ∫ ω, Z t ω ∂P = 1} →
      (∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y →
        D.functional P p T 𝓕 Y ≠ ⊥ ∧ D.functional P p T 𝓕 Y ≠ ⊤) ∧
      InformationMonotone P p T (fun 𝓖 Y => D.functional P p T 𝓖 Y) ∧
      WeakTranslationEquivariant P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      ConcaveOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      MonotoneOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      StrictOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      ContinuousOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      PositivelyHomogeneousOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal)) ∧
    (D.DualFeasible T →
      D.dualSet P q T 𝓕 ⊆ {Z : ℕ → Ω → ℝ |
        (∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, 0 ≤ Z t ω) ∧ ∫ ω, Z 1 ω ∂P = 1} →
      (∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y →
        D.functional P p T 𝓕 Y ≠ ⊥ ∧ D.functional P p T 𝓕 Y ≠ ⊤) ∧
      InformationMonotone P p T (fun 𝓖 Y => D.functional P p T 𝓖 Y) ∧
      FirstPeriodTranslationEquivariant P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      ConcaveOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      MonotoneOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      ContinuousOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      PositivelyHomogeneousOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal))
      := by sorry

end RiskFunctionals.Polyhedral
