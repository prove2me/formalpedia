-- Prove2me | Theorems.Thm_RobustMultiStop_rho_doob_decomposition
-- name    : RobustMultiStop.rho_doob_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:05.57476+00:00
-- url     : https://prove2.me/theorems/be282119-92be-464c-9d0a-7d2331a0be80
-- title:
--   (2.4), (2.5), (3.4), pp.6, 8 — the $\rho$-Doob decomposition: existence, uniqueness, increments
-- statement:
--   Throughout, $(\Omega,(\mathcal F_t)_{t\ge0},P)$ is a filtered probability space, $N$ is the exercise horizon (the paper's $T$), $\mathfrak X$ is a space of positions as in §2.1 (a linear subspace of $L^0(\Omega,\mathcal F_N,P)$, closed under $\wedge$ and $\vee$, containing all indicators $1_A$, $A\in\mathcal F_N$), and $\rho=(\rho_t)_{t\le N}$ is a DMU on $\mathfrak X$, i.e. satisfies (C1)–(C4). (In)equalities between random variables hold $P$-almost surely.
--
--   Let $n\le N$ and let $V$ be a process with $V_r\in\mathfrak X\cap L^0(\mathcal F_r)$ for $r\le n$ and $\rho_r(V_{r+1})\le V_r$ for $r<n$ (a $\rho$-supermartingale, as is $Y^*$ by the Bellman principle). Let $M^*$ be the $\rho$-Doob martingale of $V$ on $\{0,\dots,n\}$. Then
--
--   1. $M^*\in\mathcal M^\rho_0$ and $M^*_{r+1}-M^*_r=V_{r+1}-\rho_r(V_{r+1})$ for $r<n$;
--   2. there is a non-decreasing predictable $A^*$ with $A^*_0=0$ and $A^*_{r+1}-A^*_r=V_r-\rho_r(V_{r+1})$ for $r<n$, such that
--   $$V_r=V_0+M^*_r-A^*_r,\qquad r\le n;\tag{2.4}$$
--   3. uniqueness: if $M\in\mathcal M^\rho_0$ and a predictable $A$ satisfy $V_r=V_0+M_r-A_r$ for $r\le n$, then $M_r=M^*_r$ and $A_r=A^*_r$ for $r\le n$.
--
--   With $V=Y^*$ and $n=N$ this is the $\rho$-Doob decomposition (2.4) with the increments (2.5); with $V=Y^{*,l}$ and $n=N+1-l$ it gives the martingales $M^{*,l}$ of (3.4).
--
--   **Formalization Note** Predictable means $A_{r+1}\in\mathfrak X$ is $\mathcal F_r$-measurable.
--
--   Differences from the source:
--   - encoding: random variables in L⁰(Ω, F, P), (in)equalities P-a.s.; ρ_t : 𝔛 → 𝔛 ∩ L⁰(Ω, F_t, P) → a.e.-classes in Ω →ₘ[P] ℝ with their a.s. order; ρ a total map whose values matter at t ≤ N on 𝔛; "∈ L⁰(F_t)" as an F_t-measurable representative; reason: Lean convention; same instances
--   - encoding: (C2) ρ_t(1_A X) = 1_A ρ_t(X) for X ∈ 𝔛, A ∈ F_t → (C2) together with 1_A X ∈ 𝔛; reason: (C2) evaluates ρ_t at 1_A X, so the paper presupposes 1_A X ∈ 𝔛; the lattice and indicator conditions alone do not give it
--   - encoding: dates t ∈ {0, …, T} → dates t ≤ N for a horizon N; reason: renaming; N = T is the paper's setting
--   - generalization: the decomposition of Y* on {0, …, T} → any adapted ρ-supermartingale V on {0, …, n}, n ≤ N; reason: Y* is an adapted ρ-supermartingale by the Bellman principle (A.3), and V = Y*, n = N gives (2.4)–(2.5); the range n is needed for Y^{*,l}, which lives on r + l ≤ N + 1
--   - generalization: uniqueness among ρ-martingales in 𝓜^ρ_0 and non-decreasing predictable A ∈ ℋ → uniqueness among predictable A, not necessarily non-decreasing (A_0 = 0 is forced at r = 0); reason: a larger class, so the paper's uniqueness follows
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, (2.4) and (2.5), p.6; (3.4), p.8

import Mathlib
import Definitions.Def_RobustMultiStop_IsLatticeSpace
import Definitions.Def_RobustMultiStop_IsDMU
import Definitions.Def_RobustMultiStop_IsRhoMartingale
import Definitions.Def_RobustMultiStop_doob

open MeasureTheory

namespace RobustMultiStop

/-- The `ρ`-Doob decomposition (2.4)–(2.5), Laeven, Schoenmakers, Schweizer & Stadje, *Robust
Multiple Stopping — A Pathwise Duality Approach*, arXiv:2006.01802v2, p.6: "There exists a unique
`ρ`-martingale `M^{*ρ} ∈ 𝓜^ρ_0` and a non-decreasing predictable `A^{*ρ} ∈ ℋ` such that
`Y_t^* = Y_0^* + M_t^{*ρ} − A_t^{*ρ}`, `t ∈ {0, …, T}`, (2.4) … It is easy to verify that, for
`t ∈ {0, …, T − 1}`, `M^{*ρ}_{t+1} − M^{*ρ}_t = Y^*_{t+1} − ρ_t(Y^*_{t+1})`, and
`A^{*ρ}_{t+1} − A^{*ρ}_t = Y^*_t − ρ_t(Y^*_{t+1})`. (2.5)"; and (3.4), p.8, for `Y^{*,L−k+1}`.

Stated for any adapted `ρ`-supermartingale `V` (`ρ_r(V_{r+1}) ≤ V_r`) on dates `0, …, n`, `n ≤ N`:
(a) `doob ρ V n` is a null `ρ`-martingale with the increments (2.5); (b) with it, a predictable
non-decreasing `A` with increments (2.5) gives (2.4); (c) uniqueness: any null `ρ`-martingale `M` and
predictable `A` satisfying (2.4) agree with these on `0, …, n` (`A_0 = 0` is then forced at `r = 0`).

**Formalization Note** `N` is the horizon (the paper's `T`). With `n = N` and `V = Y^*` (a
`ρ`-supermartingale by (A.3)) this is (2.4)–(2.5); with `V = Y^{*,l}` and `n = N + 1 − l` it is
(3.4). Predictable: `A_{r+1} ∈ 𝔛` and `F_r`-measurable. Uniqueness is proved in a larger class (no
monotonicity of `A` assumed). -/
theorem rho_doob_decomposition {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ))
    (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ))
    (h𝔛 : IsLatticeSpace F N 𝔛) (hρ : IsDMU F N 𝔛 ρ)
    (V : ℕ → Ω →ₘ[P] ℝ) (n : ℕ) (hn : n ≤ N)
    (hV : ∀ r ≤ n, V r ∈ 𝔛 ∧ AEStronglyMeasurable[F r] (V r : Ω → ℝ) P)
    (hsup : ∀ r < n, ρ r (V (r + 1)) ≤ V r) :
    (IsRhoMartingale F N 𝔛 ρ (doob ρ V n) ∧ doob ρ V n 0 = 0 ∧
      ∀ r < n, doob ρ V n (r + 1) - doob ρ V n r = V (r + 1) - ρ r (V (r + 1))) ∧
    (∃ A : ℕ → Ω →ₘ[P] ℝ, A 0 = 0 ∧
      (∀ r < n, A (r + 1) ∈ 𝔛 ∧ AEStronglyMeasurable[F r] (A (r + 1) : Ω → ℝ) P ∧
        A r ≤ A (r + 1) ∧ A (r + 1) - A r = V r - ρ r (V (r + 1))) ∧
      ∀ r ≤ n, V r = V 0 + doob ρ V n r - A r) ∧
    (∀ M A : ℕ → Ω →ₘ[P] ℝ, IsRhoMartingale F N 𝔛 ρ M → M 0 = 0 →
      (∀ r < n, A (r + 1) ∈ 𝔛 ∧ AEStronglyMeasurable[F r] (A (r + 1) : Ω → ℝ) P) →
      (∀ r ≤ n, V r = V 0 + M r - A r) →
      ∀ r ≤ n, M r = doob ρ V n r ∧ A r = V 0 + doob ρ V n r - V r) := by sorry

end RobustMultiStop
