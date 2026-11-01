-- Prove2me | Theorems.Thm_RobustMultiStop_lemma_2_1
-- name    : RobustMultiStop.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:02.516133+00:00
-- url     : https://prove2.me/theorems/76b51204-a513-43a2-b6c9-f1731ae2de58
-- title:
--   Lemma 2.1 (Doob), p.5 — optional sampling $\rho_i(M_\tau)=M_i$ for $\rho$-martingales
-- statement:
--   Throughout, $(\Omega,(\mathcal F_t)_{t\ge0},P)$ is a filtered probability space, $N$ is the exercise horizon (the paper's $T$), $\mathfrak X$ is a space of positions as in §2.1 (a linear subspace of $L^0(\Omega,\mathcal F_N,P)$, closed under $\wedge$ and $\vee$, containing all indicators $1_A$, $A\in\mathcal F_N$), and $\rho=(\rho_t)_{t\le N}$ is a DMU on $\mathfrak X$, i.e. satisfies (C1)–(C4). (In)equalities between random variables hold $P$-almost surely.
--
--   Let $M$ be a $\rho$-martingale and $\tau$ a stopping time with $i\le\tau\le N$. Then
--
--   $$\rho_i(M_\tau)=M_i .$$
--
--   This is Doob's optional sampling theorem for the nonlinear functional $\rho$; it is the reason $\rho$-martingales can be used as penalties in the dual.
--
--   Differences from the source:
--   - encoding: random variables in L⁰(Ω, F, P), (in)equalities P-a.s.; ρ_t : 𝔛 → 𝔛 ∩ L⁰(Ω, F_t, P) → a.e.-classes in Ω →ₘ[P] ℝ with their a.s. order; ρ a total map whose values matter at t ≤ N on 𝔛; "∈ L⁰(F_t)" as an F_t-measurable representative; reason: Lean convention; same instances
--   - encoding: (C2) ρ_t(1_A X) = 1_A ρ_t(X) for X ∈ 𝔛, A ∈ F_t → (C2) together with 1_A X ∈ 𝔛; reason: (C2) evaluates ρ_t at 1_A X, so the paper presupposes 1_A X ∈ 𝔛; the lattice and indicator conditions alone do not give it
--   - encoding: dates t ∈ {0, …, T} → dates t ≤ N for a horizon N; reason: renaming; N = T is the paper's setting
--   - encoding: stopping time with i ≤ τ ≤ T → ℕ-valued F-stopping time with i ≤ τ ≤ N almost surely; reason: the paper's convention (p.4) reads inequalities between random variables P-a.s.; a surely bounded time is a special case
--   - encoding: the stopped value H_τ (and ρ_τ(X) = Σ_{j=t}^T 1_{τ=j} ρ_j(X)) → a class Z with Z = Σ_{j=0}^{N} 1_{τ=j} V_j a.s. (IsSampled); reason: the paper's own indicator-sum form; terms j < t vanish a.s. because τ ≥ t a.s.; such Z exists for every stopping time
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, Lemma 2.1, p.5

import Mathlib
import Definitions.Def_RobustMultiStop_IsLatticeSpace
import Definitions.Def_RobustMultiStop_IsDMU
import Definitions.Def_RobustMultiStop_IsRhoMartingale
import Definitions.Def_RobustMultiStop_IsSampled

open MeasureTheory

namespace RobustMultiStop

/-- Lemma 2.1 (Doob), Laeven, Schoenmakers, Schweizer & Stadje, *Robust Multiple Stopping — A
Pathwise Duality Approach*, arXiv:2006.01802v2, p.5: "Suppose `ρ` satisfies (C1)–(C4). Then, for any
`ρ`-martingale `M` and any stopping time `τ_i`, `i ≤ τ_i ≤ T`, it holds that `ρ_i(M_{τ_i}) = M_i`,
`0 ≤ i ≤ T`."

**Formalization Note** `N` is the horizon (the paper's `T`). The stopping time is `ℕ`-valued with
`i ≤ τ ≤ N` almost surely (the paper's convention for inequalities between random variables);
`M_τ` is any class `Z` with `IsSampled N M τ Z`. -/
theorem lemma_2_1 {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ))
    (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ))
    (h𝔛 : IsLatticeSpace F N 𝔛) (hρ : IsDMU F N 𝔛 ρ)
    (M : ℕ → Ω →ₘ[P] ℝ) (hM : IsRhoMartingale F N 𝔛 ρ M)
    (i : ℕ) (τ : Ω → ℕ) (hτ : IsStoppingTime F (fun ω => ((τ ω : ℕ) : WithTop ℕ)))
    (hτi : ∀ᵐ ω ∂P, i ≤ τ ω ∧ τ ω ≤ N)
    (Z : Ω →ₘ[P] ℝ) (hZ : IsSampled N M τ Z) :
    ρ i Z = M i := by sorry

end RobustMultiStop
