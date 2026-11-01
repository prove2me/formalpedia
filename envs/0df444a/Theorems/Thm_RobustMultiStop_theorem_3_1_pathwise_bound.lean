-- Prove2me | Theorems.Thm_RobustMultiStop_theorem_3_1_pathwise_bound
-- name    : RobustMultiStop.theorem_3_1_pathwise_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:16.664998+00:00
-- url     : https://prove2.me/theorems/69eb94d0-753a-4601-91db-dbda297e9da0
-- title:
--   Proof of Theorem 3.1, p.41 — pathwise bound $\max_j\sum_k(H_{j_k}+M^{*,L-k+1}_{j_{k-1}}-M^{*,L-k+1}_{j_k})\le Y^{*,L}_t$
-- statement:
--   Throughout, $(\Omega,(\mathcal F_t)_{t\ge0},P)$ is a filtered probability space, $N$ is the exercise horizon (the paper's $T$), $\mathfrak X$ is a space of positions as in §2.1 (a linear subspace of $L^0(\Omega,\mathcal F_N,P)$, closed under $\wedge$ and $\vee$, containing all indicators $1_A$, $A\in\mathcal F_N$), and $\rho=(\rho_t)_{t\le N}$ is a DMU on $\mathfrak X$, i.e. satisfies (C1)–(C4). (In)equalities between random variables hold $P$-almost surely.
--
--   Let $H\in\mathcal H$, $L\ge1$, and let $Y^{*,0}\equiv0,Y^{*,1},\dots,Y^{*,L}$ be processes satisfying the Bellman principle (3.5) for $1\le l\le L$ (with its boundary case $Y^{*,l}_r=H_r+\rho_r(Y^{*,l-1}_{r+1})$ at $r+l=N+1$), and let $M^{*,l}$ be their $\rho$-Doob martingales (3.4). Then for every $t$ with $t+L\le N+1$, almost surely,
--
--   $$\max_{t\le j_1<j_2<\dots<j_L\le N}\ \sum_{k=1}^{L}\Big(H_{j_k}+M^{*,L-k+1}_{j_{k-1}}-M^{*,L-k+1}_{j_k}\Big)\le Y^{*,L}_t,\qquad j_0=t .$$
--
--   Together with weak duality this yields the attainment (3.2) and the pathwise representation (3.3).
--
--   **Formalization Note** The printed argument on p.41 bounds each bracket $H_{j_k}+Y^{*,L-k}_{j_k}-Y^{*,L-k+1}_{j_k}$ by $0$, which is false: with $N=1$, $\rho=\mathrm{id}$, $H=(1,0)$, $L=2$, $j_1=0$ the bracket equals $1$. The statement is true by backward induction through Proposition 4.4 and (3.5); neither (P1) nor (P2) is needed.
--
--   Differences from the source:
--   - encoding: random variables in L⁰(Ω, F, P), (in)equalities P-a.s.; ρ_t : 𝔛 → 𝔛 ∩ L⁰(Ω, F_t, P) → a.e.-classes in Ω →ₘ[P] ℝ with their a.s. order; ρ a total map whose values matter at t ≤ N on 𝔛; "∈ L⁰(F_t)" as an F_t-measurable representative; reason: Lean convention; same instances
--   - encoding: (C2) ρ_t(1_A X) = 1_A ρ_t(X) for X ∈ 𝔛, A ∈ F_t → (C2) together with 1_A X ∈ 𝔛; reason: (C2) evaluates ρ_t at 1_A X, so the paper presupposes 1_A X ∈ 𝔛; the lattice and indicator conditions alone do not give it
--   - generalization: dates {0, …, T}, extended by H_j ≡ 0, F_j ≡ F_T for j > T (p.6), with rights not exercised by T becoming valueless → an arbitrary exercise horizon N: exercise dates t ≤ τ_1 < ⋯ < τ_L ≤ N, for t + L ≤ N + 1; reason: N = T, L = 1 is (2.3); N = T + L with H_j = 0, F_j = F_T and ρ_j = id for j > T (these ρ_j satisfy (C1)–(C4), (P1), (P2)) is the paper's extended problem with free rights for every t ≤ T and every L; for H of negative sign the two literal readings of the extension disagree and one of them makes (3.5) false (T = 1, ρ = id, H = (1, −1), L = 2: 1 ≠ 0), see the mission description
--   - reading: (3.5) Y_r^{*,l} = max[H_r + ρ_r(Y_{r+1}^{*,l−1}), ρ_r(Y_{r+1}^{*,l})] for all r → (3.5) for r + l ≤ N, and Y_r^{*,l} = H_r + ρ_r(Y_{r+1}^{*,l−1}) at r + l = N + 1; reason: on the horizon N no date after r can hold l rights when r + l = N + 1, so only the first branch exists; with N = T + L every r ≤ T has r + l ≤ N and the printed formula holds verbatim
--   - encoding: (3.1)–(3.3) do not print j_0 → j_0 = t (prevIdx); reason: printed in the proof, p.41 ("with j_0 = t")
--   - encoding: legs k = 1, …, L carry M^{(k)}, resp. M^{*,L−k+1} → 0-based legs k : Fin L carry M k, resp. doob ρ (Y (L − k)) (N + 1 − (L − k)); reason: index shift only: the paper's leg k is Lean's leg k − 1, and L − (k − 1) = L − k + 1
--   - generalization: Y^{*,l} the upper Snell envelopes and M^{*,l} their ρ-Doob martingales → any processes Y^{*,l} with Y^{*,0} ≡ 0 satisfying (3.5) for 1 ≤ l ≤ L, and M^{*,l} defined from them by (3.4); reason: the Snell envelopes satisfy (3.5) (milestone (3.5)), so the statement specializes to the paper's
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, proof of Theorem 3.1, p.41 ("That is, max … ≤ Y_t^{*,L}")

import Mathlib
import Definitions.Def_RobustMultiStop_IsLatticeSpace
import Definitions.Def_RobustMultiStop_IsDMU
import Definitions.Def_RobustMultiStop_IsAdapted
import Definitions.Def_RobustMultiStop_doob
import Definitions.Def_RobustMultiStop_dualMax

open MeasureTheory

namespace RobustMultiStop

/-- The pathwise upper bound in the proof of Theorem 3.1, Laeven, Schoenmakers, Schweizer & Stadje,
*Robust Multiple Stopping — A Pathwise Duality Approach*, arXiv:2006.01802v2, p.41, "That is,
`max_{t≤j_1<j_2<⋯<j_L} Σ_{k=1}^L (H_{j_k} + M^{*,L−k+1}_{j_{k−1}} − M^{*,L−k+1}_{j_k}) ≤ Y_t^{*,L}`".

For processes `Y l` with `Y 0 ≡ 0` satisfying the Bellman principle (3.5) (with its boundary case
at `r + l = N + 1`) for `1 ≤ l ≤ L`, and their `ρ`-Doob martingales `M^{*,l}` defined by (3.4), the
pathwise maximum is at most `Y_t^{*,L}` (a.s.), whenever `L` dates fit into `{t, …, N}`.

**Formalization Note** The printed route on p.41 is replaced: it marks each bracket
`H_{j_k} + Y^{*,L−k}_{j_k} − Y^{*,L−k+1}_{j_k}` as `≤ 0`, which is false (`N = 1`, `ρ = id`,
`H = (1, 0)`, `L = 2`, `j_1 = 0`: the bracket equals `1`). The statement itself is true and follows
by backward induction through Proposition 4.4 and (3.5). `j_0 = t`; the `0`-based leg `k` carries
`M^{*,L−k} = doob ρ (Y (L - k)) (N + 1 - (L - k))`. `N` is the horizon. Neither (P1) nor (P2) is
used. -/
theorem theorem_3_1_pathwise_bound {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ))
    (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ))
    (h𝔛 : IsLatticeSpace F N 𝔛) (hρ : IsDMU F N 𝔛 ρ)
    (H : ℕ → Ω →ₘ[P] ℝ) (hH : IsAdapted F N 𝔛 H) (L : ℕ) (hL : 1 ≤ L)
    (Y : ℕ → ℕ → Ω →ₘ[P] ℝ) (hY0 : ∀ r, Y 0 r = 0)
    (hB : ∀ l r, 1 ≤ l → l ≤ L → r + l ≤ N →
      Y l r = (H r + ρ r (Y (l - 1) (r + 1))) ⊔ ρ r (Y l (r + 1)))
    (hB' : ∀ l r, 1 ≤ l → l ≤ L → r + l = N + 1 → Y l r = H r + ρ r (Y (l - 1) (r + 1)))
    (t : ℕ) (ht : t + L ≤ N + 1) :
    dualMax N H t (fun k : Fin L => doob ρ (Y (L - (k : ℕ))) (N + 1 - (L - (k : ℕ))))
      ≤ Y L t := by sorry

end RobustMultiStop
