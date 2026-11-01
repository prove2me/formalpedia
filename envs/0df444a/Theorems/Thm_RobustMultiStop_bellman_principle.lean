-- Prove2me | Theorems.Thm_RobustMultiStop_bellman_principle
-- name    : RobustMultiStop.bellman_principle
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:33.245137+00:00
-- url     : https://prove2.me/theorems/513182e3-7465-49af-b3b1-a7260f5b851c
-- title:
--   (3.5), p.8 — the upper Snell envelopes exist, are attained and satisfy the Bellman principle
-- statement:
--   Throughout, $(\Omega,(\mathcal F_t)_{t\ge0},P)$ is a filtered probability space, $N$ is the exercise horizon (the paper's $T$), $\mathfrak X$ is a space of positions as in §2.1 (a linear subspace of $L^0(\Omega,\mathcal F_N,P)$, closed under $\wedge$ and $\vee$, containing all indicators $1_A$, $A\in\mathcal F_N$), and $\rho=(\rho_t)_{t\le N}$ is a DMU on $\mathfrak X$, i.e. satisfies (C1)–(C4). (In)equalities between random variables hold $P$-almost surely.
--
--   Let $H\in\mathcal H$ (of any sign). Then the upper Snell envelopes $Y^{*,l}$ of (2.2) exist (with $Y^{*,0}\equiv0$) and, for every number of rights $l\ge1$:
--
--   1. $Y^{*,l}_r\in\mathfrak X\cap L^0(\mathcal F_r)$ for $r+l\le N+1$;
--   2. the Bellman principle holds:
--   $$Y^{*,l}_r=\max\Big[H_r+\rho_r\big(Y^{*,l-1}_{r+1}\big),\ \rho_r\big(Y^{*,l}_{r+1}\big)\Big]\qquad(r+l\le N),\tag{3.5}$$
--   and $Y^{*,l}_r=H_r+\rho_r(Y^{*,l-1}_{r+1})$ when $r+l=N+1$;
--   3. for $t+l\le N+1$ the essential supremum (2.2) is attained by a stopping vector $t\le\tau_1<\dots<\tau_l\le N$ ordered for every $\omega$.
--
--   This is the dynamic-programming description of $Y^{*,l}$: the holder either exercises one right now and keeps $l-1$, or waits with all $l$. For $l=1$ it is (A.3).
--
--   **Formalization Note** At $r+l=N+1$ the $l$ remaining rights can only be exercised at $r,r+1,\dots,N$, so only the first branch exists. Only (C1)–(C4) are assumed.
--
--   Differences from the source:
--   - encoding: random variables in L⁰(Ω, F, P), (in)equalities P-a.s.; ρ_t : 𝔛 → 𝔛 ∩ L⁰(Ω, F_t, P) → a.e.-classes in Ω →ₘ[P] ℝ with their a.s. order; ρ a total map whose values matter at t ≤ N on 𝔛; "∈ L⁰(F_t)" as an F_t-measurable representative; reason: Lean convention; same instances
--   - encoding: (C2) ρ_t(1_A X) = 1_A ρ_t(X) for X ∈ 𝔛, A ∈ F_t → (C2) together with 1_A X ∈ 𝔛; reason: (C2) evaluates ρ_t at 1_A X, so the paper presupposes 1_A X ∈ 𝔛; the lattice and indicator conditions alone do not give it
--   - generalization: dates {0, …, T}, extended by H_j ≡ 0, F_j ≡ F_T for j > T (p.6), with rights not exercised by T becoming valueless → an arbitrary exercise horizon N: exercise dates t ≤ τ_1 < ⋯ < τ_L ≤ N, for t + L ≤ N + 1; reason: N = T, L = 1 is (2.3); N = T + L with H_j = 0, F_j = F_T and ρ_j = id for j > T (these ρ_j satisfy (C1)–(C4), (P1), (P2)) is the paper's extended problem with free rights for every t ≤ T and every L; for H of negative sign the two literal readings of the extension disagree and one of them makes (3.5) false (T = 1, ρ = id, H = (1, −1), L = 2: 1 ≠ 0), see the mission description
--   - reading: (3.5) Y_r^{*,l} = max[H_r + ρ_r(Y_{r+1}^{*,l−1}), ρ_r(Y_{r+1}^{*,l})] for all r → (3.5) for r + l ≤ N, and Y_r^{*,l} = H_r + ρ_r(Y_{r+1}^{*,l−1}) at r + l = N + 1; reason: on the horizon N no date after r can hold l rights when r + l = N + 1, so only the first branch exists; with N = T + L every r ≤ T has r + l ≤ N and the printed formula holds verbatim
--   - generalization: stopping vectors with t ≤ τ_1 < ⋯ < τ_L (p.5) → the supremum runs over vectors ordered almost surely, and the optimum is attained by a vector ordered for every ω; reason: the a.s. family contains the surely ordered one and has the same supremum because the optimum is attained by a surely ordered vector; the proof (p.40) uses a.s. ordering
--   - encoding: ess sup / ess inf → IsLUB / IsGLB in the lattice Ω →ₘ[P] ℝ; reason: for a family with a lower or upper bound these are the essential supremum and infimum; same objects
--   - encoding: Y^{*,L} defined as an ess sup (taken as given) → ∃ Y with IsSnell (the essential suprema exist); reason: the existence of the ess sup is a conclusion here; the attained ess sup is unique
--   - encoding: the stopped value H_τ (and ρ_τ(X) = Σ_{j=t}^T 1_{τ=j} ρ_j(X)) → a class Z with Z = Σ_{j=0}^{N} 1_{τ=j} V_j a.s. (IsSampled); reason: the paper's own indicator-sum form; terms j < t vanish a.s. because τ ≥ t a.s.; such Z exists for every stopping time
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, (3.5), p.8; p.6 ("setting Y^{*,0} ≡ 0 … Y^{*,L} can be viewed as the upper Snell envelope of the process H_t + ρ_t(Y_{t+1}^{*,L−1})"); (A.3), p.38

import Mathlib
import Definitions.Def_RobustMultiStop_IsLatticeSpace
import Definitions.Def_RobustMultiStop_IsDMU
import Definitions.Def_RobustMultiStop_IsAdapted
import Definitions.Def_RobustMultiStop_IsSampled
import Definitions.Def_RobustMultiStop_IsSureStopVec
import Definitions.Def_RobustMultiStop_IsSnell

open MeasureTheory

namespace RobustMultiStop

/-- The Bellman principle (3.5) for the upper Snell envelopes, Laeven, Schoenmakers, Schweizer &
Stadje, *Robust Multiple Stopping — A Pathwise Duality Approach*, arXiv:2006.01802v2, p.8:
"`Y^{*,L−k+1}` is the upper Snell envelope due to `L−k+1` exercise rights, satisfying the Bellman
principle, `Y_r^{*,L−k+1} = max[H_r + ρ_r(Y_{r+1}^{*,L−k}), ρ_r(Y_{r+1}^{*,L−k+1})]`. (3.5)";
p.6: "setting `Y^{*,0} ≡ 0`, `Y^{*,1} ≡ Y^*` is the upper Snell envelope of `H` due to a single
exercise right. Then, for multiple exercise rights `L ≥ 1`, `Y^{*,L}` can be viewed as the upper
Snell envelope of the process `H_t + ρ_t(Y_{t+1}^{*,L−1})` … due to only a single exercise right";
and (A.3), p.38, for one right.

Under (C1)–(C4), for every adapted `H` there are upper Snell envelopes `Y` (the essential suprema
(2.2) exist) such that, for every number of rights `l ≥ 1`:

1. `Y l r ∈ 𝔛` is `F_r`-measurable for `r + l ≤ N + 1`;
2. (3.5) holds for `r + l ≤ N`, and `Y l r = H r + ρ r (Y (l-1) (r+1))` for `r + l = N + 1`;
3. the supremum (2.2) is attained by a stopping vector ordered for every `ω`.

**Formalization Note** `N` is the exercise horizon, on which the dates `t ≤ τ_1 < ⋯ < τ_l ≤ N` run.
At `r + l = N + 1` the remaining `l` rights must be exercised at `r, r + 1, …, N`, so only the first
branch of (3.5) is available. With `N = T + L` and `H_j = 0`, `F_j = F_T`, `ρ_j = id` for `j > T`
(the paper's extension, p.6) every `r ≤ T` satisfies `r + l ≤ N` and (3.5) is the printed formula.
The paper proves (A.3) only by citation for one right and states (3.5) without proof. -/
theorem bellman_principle {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ))
    (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ))
    (h𝔛 : IsLatticeSpace F N 𝔛) (hρ : IsDMU F N 𝔛 ρ)
    (H : ℕ → Ω →ₘ[P] ℝ) (hH : IsAdapted F N 𝔛 H) :
    ∃ Y : ℕ → ℕ → Ω →ₘ[P] ℝ, IsSnell F N ρ H Y ∧
      (∀ l r, 1 ≤ l → r + l ≤ N + 1 →
        Y l r ∈ 𝔛 ∧ AEStronglyMeasurable[F r] (Y l r : Ω → ℝ) P) ∧
      (∀ l r, 1 ≤ l → r + l ≤ N →
        Y l r = (H r + ρ r (Y (l - 1) (r + 1))) ⊔ ρ r (Y l (r + 1))) ∧
      (∀ l r, 1 ≤ l → r + l = N + 1 → Y l r = H r + ρ r (Y (l - 1) (r + 1))) ∧
      (∀ l t, 1 ≤ l → t + l ≤ N + 1 →
        ∃ τ : Fin l → Ω → ℕ, IsSureStopVec F N t l τ ∧
          ∃ Z : Fin l → Ω →ₘ[P] ℝ, (∀ k, IsSampled N H (τ k) (Z k)) ∧
            Y l t = ρ t (∑ k, Z k)) := by sorry

end RobustMultiStop
