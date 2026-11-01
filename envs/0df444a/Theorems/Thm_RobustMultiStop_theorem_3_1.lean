-- Prove2me | Theorems.Thm_RobustMultiStop_theorem_3_1
-- name    : RobustMultiStop.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:18.64699+00:00
-- url     : https://prove2.me/theorems/b57af5db-73cc-488b-8e5d-db56ab4e05a5
-- title:
--   Theorem 3.1, p.8 — pathwise dual representation of robust multiple stopping: (i), (ii), (iii), (3.4), (3.5)
-- statement:
--   Throughout, $(\Omega,(\mathcal F_t)_{t\ge0},P)$ is a filtered probability space, $N$ is the exercise horizon (the paper's $T$), $\mathfrak X$ is a space of positions as in §2.1 (a linear subspace of $L^0(\Omega,\mathcal F_N,P)$, closed under $\wedge$ and $\vee$, containing all indicators $1_A$, $A\in\mathcal F_N$), and $\rho=(\rho_t)_{t\le N}$ is a DMU on $\mathfrak X$, i.e. satisfies (C1)–(C4). (In)equalities between random variables hold $P$-almost surely.
--
--   Assume in addition that $\rho$ is subadditive (P1), and let $H\in\mathcal H$ be an adapted reward process (of any sign) and $L\ge1$ the number of exercise rights. Then the upper Snell envelopes $Y^{*,l}$, $Y^{*,0}\equiv0$, of (2.2) exist, and for $1\le l\le L$:
--
--   1. $Y^{*,l}_r\in\mathfrak X\cap L^0(\mathcal F_r)$ for $r+l\le N+1$;
--   2. the Bellman principle (3.5): $Y^{*,l}_r=\max\big[H_r+\rho_r(Y^{*,l-1}_{r+1}),\ \rho_r(Y^{*,l}_{r+1})\big]$ for $r+l\le N$, and $Y^{*,l}_r=H_r+\rho_r(Y^{*,l-1}_{r+1})$ for $r+l=N+1$;
--   3. the $\rho$-Doob martingales $M^{*,l}\in\mathcal M^\rho_0$ satisfy
--   $$M^{*,l}_{r+1}-M^{*,l}_r=Y^{*,l}_{r+1}-\rho_r\big(Y^{*,l}_{r+1}\big)\qquad(r+l\le N).\tag{3.4}$$
--
--   Moreover, for every date $t$ with $t+L\le N+1$, writing $j_0=t$:
--
--   4. the essential supremum (2.2) defining $Y^{*,L}_t$ is attained by a stopping vector ordered for every $\omega$;
--   5. (i) dual representation:
--   $$Y^{*,L}_t=\inf_{M^{(1)},\dots,M^{(L)}\in\mathcal M^\rho_0}\rho_t\Big(\max_{t\le j_1<\dots<j_L\le N}\sum_{k=1}^{L}\big(H_{j_k}+M^{(k)}_{j_{k-1}}-M^{(k)}_{j_k}\big)\Big);\tag{3.1}$$
--   6. (ii) the infimum is attained:
--   $$Y^{*,L}_t=\rho_t\Big(\max_{t\le j_1<\dots<j_L\le N}\sum_{k=1}^{L}\big(H_{j_k}+M^{*,L-k+1}_{j_{k-1}}-M^{*,L-k+1}_{j_k}\big)\Big);\tag{3.2}$$
--   7. (iii) if in addition $\rho$ is sensitive (P2), the pathwise representation holds almost surely:
--   $$Y^{*,L}_t=\max_{t\le j_1<\dots<j_L\le N}\sum_{k=1}^{L}\big(H_{j_k}+M^{*,L-k+1}_{j_{k-1}}-M^{*,L-k+1}_{j_k}\big).\tag{3.3}$$
--
--   The theorem turns robust optimal multiple stopping into a minimisation over $\rho$-martingales with no stopping times in it, and under sensitivity the optimal value is a pathwise maximum; it is the basis of the primal–dual algorithm of §4 and the bounds of §5.
--
--   **Formalization Note** $N=T$, $L=1$ is the single stopping problem (2.3) (Corollary 3.2); $N=T+L$ with $H_j=0$, $\mathcal F_j=\mathcal F_T$, $\rho_j=\mathrm{id}$ for $j>T$ is the paper's extended problem. The essential supremum and infimum are `IsLUB` and `IsGLB` in the lattice of a.e.-classes.
--
--   Differences from the source:
--   - encoding: random variables in L⁰(Ω, F, P), (in)equalities P-a.s.; ρ_t : 𝔛 → 𝔛 ∩ L⁰(Ω, F_t, P) → a.e.-classes in Ω →ₘ[P] ℝ with their a.s. order; ρ a total map whose values matter at t ≤ N on 𝔛; "∈ L⁰(F_t)" as an F_t-measurable representative; reason: Lean convention; same instances
--   - encoding: (C2) ρ_t(1_A X) = 1_A ρ_t(X) for X ∈ 𝔛, A ∈ F_t → (C2) together with 1_A X ∈ 𝔛; reason: (C2) evaluates ρ_t at 1_A X, so the paper presupposes 1_A X ∈ 𝔛; the lattice and indicator conditions alone do not give it
--   - generalization: dates {0, …, T}, extended by H_j ≡ 0, F_j ≡ F_T for j > T (p.6), with rights not exercised by T becoming valueless → an arbitrary exercise horizon N: exercise dates t ≤ τ_1 < ⋯ < τ_L ≤ N, for t + L ≤ N + 1; reason: N = T, L = 1 is (2.3); N = T + L with H_j = 0, F_j = F_T and ρ_j = id for j > T (these ρ_j satisfy (C1)–(C4), (P1), (P2)) is the paper's extended problem with free rights for every t ≤ T and every L; for H of negative sign the two literal readings of the extension disagree and one of them makes (3.5) false (T = 1, ρ = id, H = (1, −1), L = 2: 1 ≠ 0), see the mission description
--   - generalization: stopping vectors with t ≤ τ_1 < ⋯ < τ_L (p.5) → the supremum runs over vectors ordered almost surely, and the optimum is attained by a vector ordered for every ω; reason: the a.s. family contains the surely ordered one and has the same supremum because the optimum is attained by a surely ordered vector; the proof (p.40) uses a.s. ordering
--   - reading: (3.5) Y_r^{*,l} = max[H_r + ρ_r(Y_{r+1}^{*,l−1}), ρ_r(Y_{r+1}^{*,l})] for all r → (3.5) for r + l ≤ N, and Y_r^{*,l} = H_r + ρ_r(Y_{r+1}^{*,l−1}) at r + l = N + 1; reason: on the horizon N no date after r can hold l rights when r + l = N + 1, so only the first branch exists; with N = T + L every r ≤ T has r + l ≤ N and the printed formula holds verbatim
--   - encoding: ess sup / ess inf → IsLUB / IsGLB in the lattice Ω →ₘ[P] ℝ; reason: for a family with a lower or upper bound these are the essential supremum and infimum; same objects
--   - encoding: (3.1)–(3.3) do not print j_0 → j_0 = t (prevIdx); reason: printed in the proof, p.41 ("with j_0 = t")
--   - encoding: legs k = 1, …, L carry M^{(k)}, resp. M^{*,L−k+1} → 0-based legs k : Fin L carry M k, resp. doob ρ (Y (L − k)) (N + 1 − (L − k)); reason: index shift only: the paper's leg k is Lean's leg k − 1, and L − (k − 1) = L − k + 1
--   - encoding: Y^{*,L} defined as an ess sup (taken as given) → ∃ Y with IsSnell (the essential suprema exist); reason: the existence of the ess sup is a conclusion here; the attained ess sup is unique
--   - encoding: the stopped value H_τ (and ρ_τ(X) = Σ_{j=t}^T 1_{τ=j} ρ_j(X)) → a class Z with Z = Σ_{j=0}^{N} 1_{τ=j} V_j a.s. (IsSampled); reason: the paper's own indicator-sum form; terms j < t vanish a.s. because τ ≥ t a.s.; such Z exists for every stopping time
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, Theorem 3.1, p.8; j_0 = t from the proof, p.41

import Mathlib
import Definitions.Def_RobustMultiStop_IsLatticeSpace
import Definitions.Def_RobustMultiStop_IsDMU
import Definitions.Def_RobustMultiStop_IsSubadditive
import Definitions.Def_RobustMultiStop_IsSensitive
import Definitions.Def_RobustMultiStop_IsAdapted
import Definitions.Def_RobustMultiStop_IsRhoMartingale
import Definitions.Def_RobustMultiStop_IsSampled
import Definitions.Def_RobustMultiStop_IsSureStopVec
import Definitions.Def_RobustMultiStop_IsSnell
import Definitions.Def_RobustMultiStop_doob
import Definitions.Def_RobustMultiStop_dualMax

open MeasureTheory

namespace RobustMultiStop

/-- Theorem 3.1, Laeven, Schoenmakers, Schweizer & Stadje, *Robust Multiple Stopping — A Pathwise
Duality Approach*, arXiv:2006.01802v2, p.8: "Suppose `ρ` satisfies (C1)–(C4) and is subadditive
(P1). Then, for any adapted process `H ∈ ℋ` and each fixed `t ∈ {0, …, T}`, (i) we have the dual
representation `Y_t^{*,L} = inf_{M^{(1)},…,M^{(L)} ∈ 𝓜^ρ_0} ρ_t(max_{t≤j_1<⋯<j_L} Σ_{k=1}^L
(H_{j_k} + M^{(k)}_{j_{k−1}} − M^{(k)}_{j_k}))`; (3.1) (ii) the dual representation's infimum is
attained: `Y_t^{*,L} = ρ_t(max … (H_{j_k} + M^{*,L−k+1}_{j_{k−1}} − M^{*,L−k+1}_{j_k}))`; (3.2)
(iii) if in addition `ρ` is sensitive (P2), we have the pathwise dual representation
`Y_t^{*,L} = max … (H_{j_k} + M^{*,L−k+1}_{j_{k−1}} − M^{*,L−k+1}_{j_k})`, almost surely; (3.3)
where the `ρ`-martingales `M^{*,L−k+1}` satisfy `M^{*,L−k+1}_{r+1} − M^{*,L−k+1}_r =
Y^{*,L−k+1}_{r+1} − ρ_r(Y^{*,L−k+1}_{r+1})`, (3.4) and `Y^{*,L−k+1}` is the upper Snell envelope due
to `L−k+1` exercise rights, satisfying the Bellman principle, `Y_r^{*,L−k+1} = max[H_r +
ρ_r(Y_{r+1}^{*,L−k}), ρ_r(Y_{r+1}^{*,L−k+1})]`. (3.5)"

The upper Snell envelopes `Y` (`IsSnell`) exist and satisfy, for `1 ≤ l ≤ L`: adaptedness; (3.5)
(with its boundary case at `r + l = N + 1`); (3.4) for the null `ρ`-martingales
`M^{*,l} = doob ρ (Y l) (N + 1 - l)`; and, for every `t` with `t + L ≤ N + 1`: attainment of (2.2) by
a surely ordered stopping vector, (i), (ii) and, under (P2), (iii).

**Formalization Note** Random variables are classes in `Ω →ₘ[P] ℝ`, so every (in)equality is a.s.;
ess sup / ess inf are `IsLUB` / `IsGLB` in this lattice. `N` is the exercise horizon: dates run in
`{0, …, N}` and `t + L ≤ N + 1` says that `L` dates fit after `t`. `N = T`, `L = 1` is the paper's
problem (2.3); `N = T + L` with `H_j = 0`, `F_j = F_T`, `ρ_j = id` for `j > T` is the paper's
extension (p.6). `H_τ = Σ_{j≤N} 1_{τ=j} H_j` (`IsSampled`). Legs are `0`-based: the paper's
superscript `L − k + 1` (`1`-based `k`) is `L - k` for the `0`-based leg `k`; `j_0 = t` (proof, p.41).
`1_A X ∈ 𝔛` is part of (C2). Stopping vectors are ordered a.s. in the supremum, and the optimum is
attained by a surely ordered one. `Y 0 ≡ 0` is the paper's `Y^{*,0} ≡ 0` (p.6). -/
theorem theorem_3_1 {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ))
    (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ))
    (h𝔛 : IsLatticeSpace F N 𝔛) (hρ : IsDMU F N 𝔛 ρ) (hP1 : IsSubadditive N 𝔛 ρ)
    (H : ℕ → Ω →ₘ[P] ℝ) (hH : IsAdapted F N 𝔛 H) (L : ℕ) (hL : 1 ≤ L) :
    ∃ Y : ℕ → ℕ → Ω →ₘ[P] ℝ, IsSnell F N ρ H Y ∧
      (∀ l r, 1 ≤ l → l ≤ L → r + l ≤ N + 1 →
        Y l r ∈ 𝔛 ∧ AEStronglyMeasurable[F r] (Y l r : Ω → ℝ) P) ∧
      (∀ l r, 1 ≤ l → l ≤ L → r + l ≤ N →
        Y l r = (H r + ρ r (Y (l - 1) (r + 1))) ⊔ ρ r (Y l (r + 1))) ∧
      (∀ l r, 1 ≤ l → l ≤ L → r + l = N + 1 → Y l r = H r + ρ r (Y (l - 1) (r + 1))) ∧
      (∀ l, 1 ≤ l → l ≤ L →
        IsRhoMartingale F N 𝔛 ρ (doob ρ (Y l) (N + 1 - l)) ∧ doob ρ (Y l) (N + 1 - l) 0 = 0 ∧
          ∀ r, r + l ≤ N → doob ρ (Y l) (N + 1 - l) (r + 1) - doob ρ (Y l) (N + 1 - l) r =
            Y l (r + 1) - ρ r (Y l (r + 1))) ∧
      (∀ t, t + L ≤ N + 1 →
        (∃ τ : Fin L → Ω → ℕ, IsSureStopVec F N t L τ ∧
          ∃ Z : Fin L → Ω →ₘ[P] ℝ, (∀ k, IsSampled N H (τ k) (Z k)) ∧
            Y L t = ρ t (∑ k, Z k)) ∧
        IsGLB {W | ∃ M : Fin L → ℕ → Ω →ₘ[P] ℝ,
          (∀ k, IsRhoMartingale F N 𝔛 ρ (M k) ∧ M k 0 = 0) ∧ W = ρ t (dualMax N H t M)} (Y L t) ∧
        Y L t = ρ t (dualMax N H t
          (fun k : Fin L => doob ρ (Y (L - (k : ℕ))) (N + 1 - (L - (k : ℕ))))) ∧
        (IsSensitive N 𝔛 ρ →
          Y L t = dualMax N H t
            (fun k : Fin L => doob ρ (Y (L - (k : ℕ))) (N + 1 - (L - (k : ℕ)))))) := by sorry

end RobustMultiStop
