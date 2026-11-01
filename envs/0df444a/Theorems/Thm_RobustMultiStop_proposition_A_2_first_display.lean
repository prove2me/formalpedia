-- Prove2me | Theorems.Thm_RobustMultiStop_proposition_A_2_first_display
-- name    : RobustMultiStop.proposition_A_2_first_display
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:07.08176+00:00
-- url     : https://prove2.me/theorems/d249f8ff-04d2-4041-8041-a83c216c4322
-- title:
--   Proof of Proposition A.2, p.39 — $\rho_t(H_\tau+M_N-M_\tau)=\rho_t(H_\tau)$
-- statement:
--   Throughout, $(\Omega,(\mathcal F_t)_{t\ge0},P)$ is a filtered probability space, $N$ is the exercise horizon (the paper's $T$), $\mathfrak X$ is a space of positions as in §2.1 (a linear subspace of $L^0(\Omega,\mathcal F_N,P)$, closed under $\wedge$ and $\vee$, containing all indicators $1_A$, $A\in\mathcal F_N$), and $\rho=(\rho_t)_{t\le N}$ is a DMU on $\mathfrak X$, i.e. satisfies (C1)–(C4). (In)equalities between random variables hold $P$-almost surely.
--
--   Let $H\in\mathcal H$, let $M$ be a $\rho$-martingale and let $\tau$ be a stopping time with $t\le\tau\le N$. Then
--
--   $$\rho_t\big(H_\tau+M_N-M_\tau\big)=\rho_t\big(H_\tau\big).$$
--
--   Adding the terminal increment of a $\rho$-martingale after the stopping time does not change the evaluation; this is the first step of the dual representation for one exercise right and of Lemma B.1.
--
--   Differences from the source:
--   - encoding: random variables in L⁰(Ω, F, P), (in)equalities P-a.s.; ρ_t : 𝔛 → 𝔛 ∩ L⁰(Ω, F_t, P) → a.e.-classes in Ω →ₘ[P] ℝ with their a.s. order; ρ a total map whose values matter at t ≤ N on 𝔛; "∈ L⁰(F_t)" as an F_t-measurable representative; reason: Lean convention; same instances
--   - encoding: (C2) ρ_t(1_A X) = 1_A ρ_t(X) for X ∈ 𝔛, A ∈ F_t → (C2) together with 1_A X ∈ 𝔛; reason: (C2) evaluates ρ_t at 1_A X, so the paper presupposes 1_A X ∈ 𝔛; the lattice and indicator conditions alone do not give it
--   - encoding: dates t ∈ {0, …, T} → dates t ≤ N for a horizon N; reason: renaming; N = T is the paper's setting
--   - encoding: stopping time with i ≤ τ ≤ T → ℕ-valued F-stopping time with i ≤ τ ≤ N almost surely; reason: the paper's convention (p.4) reads inequalities between random variables P-a.s.; a surely bounded time is a special case
--   - encoding: the stopped value H_τ (and ρ_τ(X) = Σ_{j=t}^T 1_{τ=j} ρ_j(X)) → a class Z with Z = Σ_{j=0}^{N} 1_{τ=j} V_j a.s. (IsSampled); reason: the paper's own indicator-sum form; terms j < t vanish a.s. because τ ≥ t a.s.; such Z exists for every stopping time
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, proof of Proposition A.2, first display, p.39

import Mathlib
import Definitions.Def_RobustMultiStop_IsLatticeSpace
import Definitions.Def_RobustMultiStop_IsDMU
import Definitions.Def_RobustMultiStop_IsAdapted
import Definitions.Def_RobustMultiStop_IsRhoMartingale
import Definitions.Def_RobustMultiStop_IsSampled

open MeasureTheory

namespace RobustMultiStop

/-- Proof of Proposition A.2, first display, Laeven, Schoenmakers, Schweizer & Stadje, *Robust
Multiple Stopping — A Pathwise Duality Approach*, arXiv:2006.01802v2, p.39: "For any `ρ`-martingale
`M` and any stopping time `τ ≥ t`, we have by Lemmas 2.1 and 2.2 that …
`ρ_t(H_τ + M_T − M_τ) = ρ_t ∘ ρ_τ(H_τ + M_T − M_τ) = ρ_t(H_τ − M_τ + ρ_τ(M_T)) = ρ_t(H_τ)`."

**Formalization Note** `N` is the horizon (the paper's `T`); `t ≤ τ ≤ N` a.s.; `H_τ`, `M_τ` are
classes with `IsSampled`. Only (C1)–(C4) are assumed. -/
theorem proposition_A_2_first_display {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ))
    (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ))
    (h𝔛 : IsLatticeSpace F N 𝔛) (hρ : IsDMU F N 𝔛 ρ)
    (H : ℕ → Ω →ₘ[P] ℝ) (hH : IsAdapted F N 𝔛 H)
    (M : ℕ → Ω →ₘ[P] ℝ) (hM : IsRhoMartingale F N 𝔛 ρ M)
    (t : ℕ) (τ : Ω → ℕ) (hτ : IsStoppingTime F (fun ω => ((τ ω : ℕ) : WithTop ℕ)))
    (hτt : ∀ᵐ ω ∂P, t ≤ τ ω ∧ τ ω ≤ N)
    (Zh Zm : Ω →ₘ[P] ℝ) (hZh : IsSampled N H τ Zh) (hZm : IsSampled N M τ Zm) :
    ρ t (Zh + M N - Zm) = ρ t Zh := by sorry

end RobustMultiStop
