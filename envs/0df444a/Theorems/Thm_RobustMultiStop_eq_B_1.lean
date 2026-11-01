-- Prove2me | Theorems.Thm_RobustMultiStop_eq_B_1
-- name    : RobustMultiStop.eq_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:20.667952+00:00
-- url     : https://prove2.me/theorems/59cae18a-9e75-48ca-939c-e2a84faefb04
-- title:
--   (B.1), p.40 — $\rho_t(\sum_k H_{\tau_k})\le\rho_t(\sum_k(H_{\tau_k}+M^{(k)}_{\tau_{k-1}}-M^{(k)}_{\tau_k}))$
-- statement:
--   Throughout, $(\Omega,(\mathcal F_t)_{t\ge0},P)$ is a filtered probability space, $N$ is the exercise horizon (the paper's $T$), $\mathfrak X$ is a space of positions as in §2.1 (a linear subspace of $L^0(\Omega,\mathcal F_N,P)$, closed under $\wedge$ and $\vee$, containing all indicators $1_A$, $A\in\mathcal F_N$), and $\rho=(\rho_t)_{t\le N}$ is a DMU on $\mathfrak X$, i.e. satisfies (C1)–(C4). (In)equalities between random variables hold $P$-almost surely.
--
--   Assume in addition that $\rho$ is subadditive (P1). Let $H\in\mathcal H$, $L\ge1$, let $t\le\tau_1<\tau_2<\dots<\tau_L\le N$ almost surely be stopping times and $M^{(1)},\dots,M^{(L)}$ be $\rho$-martingales. With $\tau_0:=t$,
--
--   $$\rho_t\Big(\sum_{k=1}^{L}H_{\tau_k}\Big)\le\rho_t\Big(\sum_{k=1}^{L}\big(H_{\tau_k}+M^{(k)}_{\tau_{k-1}}-M^{(k)}_{\tau_k}\big)\Big). \tag{B.1}$$
--
--   This is weak duality for $L$ exercise rights along a fixed strategy; maximising the right-hand side pathwise gives (B.3).
--
--   Differences from the source:
--   - encoding: random variables in L⁰(Ω, F, P), (in)equalities P-a.s.; ρ_t : 𝔛 → 𝔛 ∩ L⁰(Ω, F_t, P) → a.e.-classes in Ω →ₘ[P] ℝ with their a.s. order; ρ a total map whose values matter at t ≤ N on 𝔛; "∈ L⁰(F_t)" as an F_t-measurable representative; reason: Lean convention; same instances
--   - encoding: (C2) ρ_t(1_A X) = 1_A ρ_t(X) for X ∈ 𝔛, A ∈ F_t → (C2) together with 1_A X ∈ 𝔛; reason: (C2) evaluates ρ_t at 1_A X, so the paper presupposes 1_A X ∈ 𝔛; the lattice and indicator conditions alone do not give it
--   - generalization: dates {0, …, T}, extended by H_j ≡ 0, F_j ≡ F_T for j > T (p.6), with rights not exercised by T becoming valueless → an arbitrary exercise horizon N: exercise dates t ≤ τ_1 < ⋯ < τ_L ≤ N, for t + L ≤ N + 1; reason: N = T, L = 1 is (2.3); N = T + L with H_j = 0, F_j = F_T and ρ_j = id for j > T (these ρ_j satisfy (C1)–(C4), (P1), (P2)) is the paper's extended problem with free rights for every t ≤ T and every L; for H of negative sign the two literal readings of the extension disagree and one of them makes (3.5) false (T = 1, ρ = id, H = (1, −1), L = 2: 1 ≠ 0), see the mission description
--   - encoding: the stopped value H_τ (and ρ_τ(X) = Σ_{j=t}^T 1_{τ=j} ρ_j(X)) → a class Z with Z = Σ_{j=0}^{N} 1_{τ=j} V_j a.s. (IsSampled); reason: the paper's own indicator-sum form; terms j < t vanish a.s. because τ ≥ t a.s.; such Z exists for every stopping time
--   - encoding: legs k = 1, …, L carry M^{(k)}, resp. M^{*,L−k+1} → 0-based legs k : Fin L carry M k, resp. doob ρ (Y (L − k)) (N + 1 − (L − k)); reason: index shift only: the paper's leg k is Lean's leg k − 1, and L − (k − 1) = L − k + 1
--   - reading: τ_0 is not defined in (B.1) → τ_0 := t; reason: forced by "For L = 1, this statement boils down to Lemma B.1", whose penalty is M_t − M_τ
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, proof of Theorem 3.1, (B.1), p.40

import Mathlib
import Definitions.Def_RobustMultiStop_IsLatticeSpace
import Definitions.Def_RobustMultiStop_IsDMU
import Definitions.Def_RobustMultiStop_IsSubadditive
import Definitions.Def_RobustMultiStop_IsAdapted
import Definitions.Def_RobustMultiStop_IsRhoMartingale
import Definitions.Def_RobustMultiStop_IsSampled
import Definitions.Def_RobustMultiStop_IsStopVec
import Definitions.Def_RobustMultiStop_prevIdx

open MeasureTheory

namespace RobustMultiStop

/-- Display (B.1), Laeven, Schoenmakers, Schweizer & Stadje, *Robust Multiple Stopping — A Pathwise
Duality Approach*, arXiv:2006.01802v2, proof of Theorem 3.1, p.40: "for any `t = 0, …, T`, any
sequence of stopping times with `t ≤ τ_1 < τ_2 < ⋯ < τ_L` a.s., and any set of `ρ`-martingales
`M^{(1)}, …, M^{(L)}`, we have
`ρ_t(Σ_{k=1}^L H_{τ_k}) ≤ ρ_t(Σ_{k=1}^L (H_{τ_k} + M^{(k)}_{τ_{k−1}} − M^{(k)}_{τ_k}))`. (B.1)"

**Formalization Note** `τ_0 := t` (forced by "For `L = 1`, this statement boils down to Lemma B.1");
the vector is `0`-based (`τ k`, `M k` for the paper's `τ_{k+1}`, `M^{(k+1)}`), and `τ_{k−1}` is
`prevIdx (fun _ => t) τ k`. The times lie in `{t, …, N}` a.s. (`N` the horizon); `H_{τ_k}`,
`M^{(k)}_{τ_{k−1}}`, `M^{(k)}_{τ_k}` are the classes `Zh k`, `Zp k`, `Zm k` given by `IsSampled`.
Assumptions: (C1)–(C4) and (P1), as in Theorem 3.1. -/
theorem eq_B_1 {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ))
    (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ))
    (h𝔛 : IsLatticeSpace F N 𝔛) (hρ : IsDMU F N 𝔛 ρ) (hP1 : IsSubadditive N 𝔛 ρ)
    (H : ℕ → Ω →ₘ[P] ℝ) (hH : IsAdapted F N 𝔛 H)
    (L : ℕ) (hL : 1 ≤ L) (t : ℕ) (τ : Fin L → Ω → ℕ) (hτ : IsStopVec P F N t L τ)
    (M : Fin L → ℕ → Ω →ₘ[P] ℝ) (hM : ∀ k, IsRhoMartingale F N 𝔛 ρ (M k))
    (Zh Zp Zm : Fin L → Ω →ₘ[P] ℝ)
    (hZh : ∀ k, IsSampled N H (τ k) (Zh k))
    (hZp : ∀ k, IsSampled N (M k) (prevIdx (fun _ => t) τ k) (Zp k))
    (hZm : ∀ k, IsSampled N (M k) (τ k) (Zm k)) :
    ρ t (∑ k, Zh k) ≤ ρ t (∑ k, (Zh k + Zp k - Zm k)) := by sorry

end RobustMultiStop
