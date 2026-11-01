-- Prove2me | Theorems.Thm_RobustMultiStop_lemma_2_2
-- name    : RobustMultiStop.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:30:40.284262+00:00
-- url     : https://prove2.me/theorems/937c332e-5ea4-4f63-a361-43bc01b62351
-- title:
--   Lemma 2.2, p.5 — the stopped functional $\rho_\tau$: $\mathcal F_\tau$-valued, $\rho_t=\rho_t\circ\rho_\tau$, translation invariant
-- statement:
--   Throughout, $(\Omega,(\mathcal F_t)_{t\ge0},P)$ is a filtered probability space, $N$ is the exercise horizon (the paper's $T$), $\mathfrak X$ is a space of positions as in §2.1 (a linear subspace of $L^0(\Omega,\mathcal F_N,P)$, closed under $\wedge$ and $\vee$, containing all indicators $1_A$, $A\in\mathcal F_N$), and $\rho=(\rho_t)_{t\le N}$ is a DMU on $\mathfrak X$, i.e. satisfies (C1)–(C4). (In)equalities between random variables hold $P$-almost surely.
--
--   Fix $t$ and a stopping time $\tau$ with $t\le\tau\le N$, and define $\rho_\tau(X):=\sum_{j=t}^{N}1_{\{\tau=j\}}\rho_j(X)$. Then
--
--   1. $\rho_\tau$ maps $\mathfrak X$ into $\mathfrak X\cap L^0(\mathcal F_\tau)$;
--   2. $\mathcal F_\tau\supset\mathcal F_t$: every $\mathcal F_t$-measurable variable is $\mathcal F_\tau$-measurable;
--   3. (i) $\rho_t(\rho_\tau(X))=\rho_t(X)$ for $X\in\mathfrak X$;
--   4. (ii) $\rho_\tau(X+Y)=X+\rho_\tau(Y)$ for $X,Y\in\mathfrak X$ with $X$ $\mathcal F_\tau$-measurable.
--
--   The lemma carries recursiveness (C3) and translation invariance (C4) over to stopping times.
--
--   Differences from the source:
--   - encoding: random variables in L⁰(Ω, F, P), (in)equalities P-a.s.; ρ_t : 𝔛 → 𝔛 ∩ L⁰(Ω, F_t, P) → a.e.-classes in Ω →ₘ[P] ℝ with their a.s. order; ρ a total map whose values matter at t ≤ N on 𝔛; "∈ L⁰(F_t)" as an F_t-measurable representative; reason: Lean convention; same instances
--   - encoding: (C2) ρ_t(1_A X) = 1_A ρ_t(X) for X ∈ 𝔛, A ∈ F_t → (C2) together with 1_A X ∈ 𝔛; reason: (C2) evaluates ρ_t at 1_A X, so the paper presupposes 1_A X ∈ 𝔛; the lattice and indicator conditions alone do not give it
--   - encoding: dates t ∈ {0, …, T} → dates t ≤ N for a horizon N; reason: renaming; N = T is the paper's setting
--   - encoding: stopping time with i ≤ τ ≤ T → ℕ-valued F-stopping time with i ≤ τ ≤ N almost surely; reason: the paper's convention (p.4) reads inequalities between random variables P-a.s.; a surely bounded time is a special case
--   - encoding: the stopped value H_τ (and ρ_τ(X) = Σ_{j=t}^T 1_{τ=j} ρ_j(X)) → a class Z with Z = Σ_{j=0}^{N} 1_{τ=j} V_j a.s. (IsSampled); reason: the paper's own indicator-sum form; terms j < t vanish a.s. because τ ≥ t a.s.; such Z exists for every stopping time
--   - encoding: F_τ ⊃ F_t (an inclusion of σ-algebras) → every class with an F_t-measurable representative has an F_τ-measurable representative; reason: statements about classes; with t ≤ τ only a.s. the sure inclusion can fail on a null set, the a.e. form is what the lemma uses
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, Lemma 2.2, p.5

import Mathlib
import Definitions.Def_RobustMultiStop_IsLatticeSpace
import Definitions.Def_RobustMultiStop_IsDMU
import Definitions.Def_RobustMultiStop_IsSampled

open MeasureTheory

namespace RobustMultiStop

/-- Lemma 2.2, Laeven, Schoenmakers, Schweizer & Stadje, *Robust Multiple Stopping — A Pathwise
Duality Approach*, arXiv:2006.01802v2, p.5: "Let `ρ` satisfy (C1)–(C4), and let `t ∈ {0, …, T}` be
fixed. Consider, for any stopping time `τ`, `t ≤ τ ≤ T`, the functional
`ρ_τ(X) := Σ_{j=t}^T 1_{τ=j} ρ_j(X)`. Then, `ρ_τ` acts from `F_T → F_τ ⊃ F_t`, and
(i) `ρ_τ` satisfies `ρ_t = ρ_t ∘ ρ_τ`; (ii) `ρ_τ(X + Y) = X + ρ_τ(Y)`, for `X ∈ F_τ`, `Y ∈ F_T`."

The four conjuncts are: `ρ_τ` maps `𝔛` into `𝔛 ∩ L⁰(F_τ)`; `F_t`-measurable classes are
`F_τ`-measurable (`F_τ ⊃ F_t`); (i); (ii).

**Formalization Note** `N` is the horizon (the paper's `T`). `ρ_τ(X)` is any class `Z` with
`IsSampled N (fun j => ρ j X) τ Z`; since `t ≤ τ` a.s., the sum from `0` equals the paper's sum from
`t` a.s. `F_τ` is Mathlib's `IsStoppingTime.measurableSpace`, and "`∈ F_τ`" means the class has an
`F_τ`-measurable representative. `t ≤ τ ≤ N` holds almost surely (the paper's convention). -/
theorem lemma_2_2 {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ))
    (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ))
    (h𝔛 : IsLatticeSpace F N 𝔛) (hρ : IsDMU F N 𝔛 ρ)
    (t : ℕ) (τ : Ω → ℕ) (hτ : IsStoppingTime F (fun ω => ((τ ω : ℕ) : WithTop ℕ)))
    (hτt : ∀ᵐ ω ∂P, t ≤ τ ω ∧ τ ω ≤ N) :
    (∀ X ∈ 𝔛, ∀ Z : Ω →ₘ[P] ℝ, IsSampled N (fun j => ρ j X) τ Z →
        Z ∈ 𝔛 ∧ AEStronglyMeasurable[hτ.measurableSpace] (Z : Ω → ℝ) P) ∧
      (∀ X : Ω →ₘ[P] ℝ, AEStronglyMeasurable[F t] (X : Ω → ℝ) P →
        AEStronglyMeasurable[hτ.measurableSpace] (X : Ω → ℝ) P) ∧
      (∀ X ∈ 𝔛, ∀ Z : Ω →ₘ[P] ℝ, IsSampled N (fun j => ρ j X) τ Z → ρ t Z = ρ t X) ∧
      (∀ X ∈ 𝔛, ∀ Y ∈ 𝔛, AEStronglyMeasurable[hτ.measurableSpace] (X : Ω → ℝ) P →
        ∀ Z₁ Z₂ : Ω →ₘ[P] ℝ, IsSampled N (fun j => ρ j (X + Y)) τ Z₁ →
          IsSampled N (fun j => ρ j Y) τ Z₂ → Z₁ = X + Z₂) := by sorry

end RobustMultiStop
