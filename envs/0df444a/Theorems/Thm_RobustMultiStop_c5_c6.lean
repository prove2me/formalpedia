-- Prove2me | Theorems.Thm_RobustMultiStop_c5_c6
-- name    : RobustMultiStop.c5_c6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:30:24.135487+00:00
-- url     : https://prove2.me/theorems/d7839902-05b9-4a95-a5f8-8184917b8312
-- title:
--   (C5), (C6), p.5 — normalization $\rho_t(0)=0$ and $\mathcal F_t$-invariance $\rho_t(X)=X$
-- statement:
--   Throughout, $(\Omega,(\mathcal F_t)_{t\ge0},P)$ is a filtered probability space, $N$ is the exercise horizon (the paper's $T$), $\mathfrak X$ is a space of positions as in §2.1 (a linear subspace of $L^0(\Omega,\mathcal F_N,P)$, closed under $\wedge$ and $\vee$, containing all indicators $1_A$, $A\in\mathcal F_N$), and $\rho=(\rho_t)_{t\le N}$ is a DMU on $\mathfrak X$, i.e. satisfies (C1)–(C4). (In)equalities between random variables hold $P$-almost surely.
--
--   Then for every $t\le N$:
--
--   1. (C5) $\rho_t(0)=0$ (normalization);
--   2. (C6) $\rho_t(X)=X$ for every $\mathcal F_t$-measurable $X\in\mathfrak X$ ($\mathcal F_t$-invariance).
--
--   These two consequences of (C2) and (C4) are used throughout the paper, e.g. to see that a $\rho$-martingale stays constant once it is measurable.
--
--   Differences from the source:
--   - encoding: random variables in L⁰(Ω, F, P), (in)equalities P-a.s.; ρ_t : 𝔛 → 𝔛 ∩ L⁰(Ω, F_t, P) → a.e.-classes in Ω →ₘ[P] ℝ with their a.s. order; ρ a total map whose values matter at t ≤ N on 𝔛; "∈ L⁰(F_t)" as an F_t-measurable representative; reason: Lean convention; same instances
--   - encoding: (C2) ρ_t(1_A X) = 1_A ρ_t(X) for X ∈ 𝔛, A ∈ F_t → (C2) together with 1_A X ∈ 𝔛; reason: (C2) evaluates ρ_t at 1_A X, so the paper presupposes 1_A X ∈ 𝔛; the lattice and indicator conditions alone do not give it
--   - encoding: dates t ∈ {0, …, T} → dates t ≤ N for a horizon N; reason: renaming; N = T is the paper's setting
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, (C5) and (C6), p.5

import Mathlib
import Definitions.Def_RobustMultiStop_IsDMU

open MeasureTheory

namespace RobustMultiStop

/-- (C5) and (C6), Laeven, Schoenmakers, Schweizer & Stadje, *Robust Multiple Stopping — A Pathwise
Duality Approach*, arXiv:2006.01802v2, §2.1, p.5, "the following implications of (C2) and (C4)":

* (C5) `ρ_t(0) = 0` for all `t ∈ {0, …, T}` (normalization);
* (C6) `ρ_t(X) = X` for all `X ∈ 𝔛` with `X ∈ F_t` and `t ∈ {0, …, T}` (`F_t`-invariance).

**Formalization Note** `N` is the horizon (the paper's `T`); `X ∈ F_t` means the class `X` has an
`F t`-measurable representative. -/
theorem c5_c6 {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    (F : Filtration ℕ m0) (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ))
    (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ)) (hρ : IsDMU F N 𝔛 ρ) :
    ∀ t ≤ N, ρ t 0 = 0 ∧
      ∀ X ∈ 𝔛, AEStronglyMeasurable[F t] (X : Ω → ℝ) P → ρ t X = X := by sorry

end RobustMultiStop
