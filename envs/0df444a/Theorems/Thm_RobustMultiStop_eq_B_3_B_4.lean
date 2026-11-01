-- Prove2me | Theorems.Thm_RobustMultiStop_eq_B_3_B_4
-- name    : RobustMultiStop.eq_B_3_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:50.393981+00:00
-- url     : https://prove2.me/theorems/a78122bb-4fff-468a-902c-a88bac6c34bb
-- title:
--   (B.3), (B.4), p.40 — weak duality $Y^{*,L}_t\le\rho_t(\max_{j}\sum_k(H_{j_k}+M^{(k)}_{j_{k-1}}-M^{(k)}_{j_k}))$
-- statement:
--   Throughout, $(\Omega,(\mathcal F_t)_{t\ge0},P)$ is a filtered probability space, $N$ is the exercise horizon (the paper's $T$), $\mathfrak X$ is a space of positions as in §2.1 (a linear subspace of $L^0(\Omega,\mathcal F_N,P)$, closed under $\wedge$ and $\vee$, containing all indicators $1_A$, $A\in\mathcal F_N$), and $\rho=(\rho_t)_{t\le N}$ is a DMU on $\mathfrak X$, i.e. satisfies (C1)–(C4). (In)equalities between random variables hold $P$-almost surely.
--
--   Assume in addition that $\rho$ is subadditive (P1), let $H\in\mathcal H$, $L\ge1$, and write, for processes $M^{(1)},\dots,M^{(L)}$ and $j_0=t$,
--
--   $$D_t(M):=\max_{t\le j_1<j_2<\dots<j_L\le N}\sum_{k=1}^{L}\Big(H_{j_k}+M^{(k)}_{j_{k-1}}-M^{(k)}_{j_k}\Big).$$
--
--   1. For all $\rho$-martingales $M^{(1)},\dots,M^{(L)}$ and every stopping vector $t\le\tau_1<\dots<\tau_L\le N$ (a.s.): $\rho_t\big(\sum_kH_{\tau_k}\big)\le\rho_t(D_t(M))$.
--   2. Hence, if $Y$ are the upper Snell envelopes and $t+L\le N+1$:
--   $$Y^{*,L}_t\le\rho_t\big(D_t(M)\big)\ \text{ for all }\rho\text{-martingales }M^{(k)},\tag{B.3}$$
--   $$Y^{*,L}_t\le\inf_{M^{(1)},\dots,M^{(L)}\in\mathcal M^\rho_0}\rho_t\big(D_t(M)\big).\tag{B.4}$$
--
--   This is the weak-duality half of Theorem 3.1(i).
--
--   Differences from the source:
--   - encoding: random variables in L⁰(Ω, F, P), (in)equalities P-a.s.; ρ_t : 𝔛 → 𝔛 ∩ L⁰(Ω, F_t, P) → a.e.-classes in Ω →ₘ[P] ℝ with their a.s. order; ρ a total map whose values matter at t ≤ N on 𝔛; "∈ L⁰(F_t)" as an F_t-measurable representative; reason: Lean convention; same instances
--   - encoding: (C2) ρ_t(1_A X) = 1_A ρ_t(X) for X ∈ 𝔛, A ∈ F_t → (C2) together with 1_A X ∈ 𝔛; reason: (C2) evaluates ρ_t at 1_A X, so the paper presupposes 1_A X ∈ 𝔛; the lattice and indicator conditions alone do not give it
--   - generalization: dates {0, …, T}, extended by H_j ≡ 0, F_j ≡ F_T for j > T (p.6), with rights not exercised by T becoming valueless → an arbitrary exercise horizon N: exercise dates t ≤ τ_1 < ⋯ < τ_L ≤ N, for t + L ≤ N + 1; reason: N = T, L = 1 is (2.3); N = T + L with H_j = 0, F_j = F_T and ρ_j = id for j > T (these ρ_j satisfy (C1)–(C4), (P1), (P2)) is the paper's extended problem with free rights for every t ≤ T and every L; for H of negative sign the two literal readings of the extension disagree and one of them makes (3.5) false (T = 1, ρ = id, H = (1, −1), L = 2: 1 ≠ 0), see the mission description
--   - encoding: the stopped value H_τ (and ρ_τ(X) = Σ_{j=t}^T 1_{τ=j} ρ_j(X)) → a class Z with Z = Σ_{j=0}^{N} 1_{τ=j} V_j a.s. (IsSampled); reason: the paper's own indicator-sum form; terms j < t vanish a.s. because τ ≥ t a.s.; such Z exists for every stopping time
--   - encoding: legs k = 1, …, L carry M^{(k)}, resp. M^{*,L−k+1} → 0-based legs k : Fin L carry M k, resp. doob ρ (Y (L − k)) (N + 1 − (L − k)); reason: index shift only: the paper's leg k is Lean's leg k − 1, and L − (k − 1) = L − k + 1
--   - encoding: (3.1)–(3.3) do not print j_0 → j_0 = t (prevIdx); reason: printed in the proof, p.41 ("with j_0 = t")
--   - encoding: ess sup / ess inf → IsLUB / IsGLB in the lattice Ω →ₘ[P] ℝ; reason: for a family with a lower or upper bound these are the essential supremum and infimum; same objects
--   - generalization: (B.3) for the Snell envelope Y^{*,L}_t → also the bound for each stopping vector before the supremum is taken (clause 1); reason: (B.3) is the supremum of clause 1 over stopping vectors; the extra clause is the paper's own intermediate step
--   - encoding: Y^{*,L} given as an ess sup → any Y with IsSnell; reason: the ess sup exists (milestone (3.5)) and is unique, so this is the same object
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, proof of Theorem 3.1, (B.3) and (B.4), p.40

import Mathlib
import Definitions.Def_RobustMultiStop_IsLatticeSpace
import Definitions.Def_RobustMultiStop_IsDMU
import Definitions.Def_RobustMultiStop_IsSubadditive
import Definitions.Def_RobustMultiStop_IsAdapted
import Definitions.Def_RobustMultiStop_IsRhoMartingale
import Definitions.Def_RobustMultiStop_IsSampled
import Definitions.Def_RobustMultiStop_IsStopVec
import Definitions.Def_RobustMultiStop_IsSnell
import Definitions.Def_RobustMultiStop_dualMax

open MeasureTheory

namespace RobustMultiStop

/-- Displays (B.3) and (B.4), weak duality, Laeven, Schoenmakers, Schweizer & Stadje, *Robust
Multiple Stopping — A Pathwise Duality Approach*, arXiv:2006.01802v2, proof of Theorem 3.1, p.40:
"As a corollary, we obtain
`Y_t^{*,L} ≤ ρ_t(max_{t≤j_1<j_2<⋯<j_L} Σ_{k=1}^L (H_{j_k} + M^{(k)}_{j_{k−1}} − M^{(k)}_{j_k}))`, (B.3)
… Since the `ρ`-martingales `M^{(k)}` are arbitrary, we thus arrive at
`Y_t^{*,L} ≤ inf_{M^{(1)},…,M^{(L)} ∈ 𝓜^ρ_0} ρ_t(max_{t≤j_1<j_2<⋯<j_L} Σ_{k=1}^L (…))`. (B.4)"

The first conjunct is the bound for each stopping vector, before the supremum is taken; the second
is (B.3) for every `ρ`-martingale family and (B.4) (a lower bound of the dual family over null
`ρ`-martingales), for the upper Snell envelope `Y`.

**Formalization Note** `N` is the horizon; `j_0 = t` (proof, p.41); legs are `0`-based; the maximum
is `dualMax`. The ess sup is `IsLUB`, the ess inf a lower bound in `Ω →ₘ[P] ℝ`. `t + L ≤ N + 1`
says that `L` dates fit into `{t, …, N}`. Assumptions: (C1)–(C4) and (P1). -/
theorem eq_B_3_B_4 {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ))
    (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ))
    (h𝔛 : IsLatticeSpace F N 𝔛) (hρ : IsDMU F N 𝔛 ρ) (hP1 : IsSubadditive N 𝔛 ρ)
    (H : ℕ → Ω →ₘ[P] ℝ) (hH : IsAdapted F N 𝔛 H) (L : ℕ) (hL : 1 ≤ L) (t : ℕ) :
    (∀ M : Fin L → ℕ → Ω →ₘ[P] ℝ, (∀ k, IsRhoMartingale F N 𝔛 ρ (M k)) →
      ∀ τ : Fin L → Ω → ℕ, IsStopVec P F N t L τ →
        ∀ Zh : Fin L → Ω →ₘ[P] ℝ, (∀ k, IsSampled N H (τ k) (Zh k)) →
          ρ t (∑ k, Zh k) ≤ ρ t (dualMax N H t M)) ∧
    (∀ Y : ℕ → ℕ → Ω →ₘ[P] ℝ, IsSnell F N ρ H Y → t + L ≤ N + 1 →
      (∀ M : Fin L → ℕ → Ω →ₘ[P] ℝ, (∀ k, IsRhoMartingale F N 𝔛 ρ (M k)) →
        Y L t ≤ ρ t (dualMax N H t M)) ∧
      Y L t ∈ lowerBounds {W | ∃ M : Fin L → ℕ → Ω →ₘ[P] ℝ,
        (∀ k, IsRhoMartingale F N 𝔛 ρ (M k) ∧ M k 0 = 0) ∧ W = ρ t (dualMax N H t M)}) := by sorry

end RobustMultiStop
