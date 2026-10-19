-- Prove2me | Theorems.Thm_SimpleCorrMFG_Conv_eq_6_3
-- name    : SimpleCorrMFG.Conv.eq_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:29.242766+00:00
-- url     : https://prove2.me/theorems/d4616dae-a75f-4075-b7d5-5ae934e8ffaf
-- title:
--   (6.3), p. 22 — $\mathbb E_N[\mathrm{dist}(\hat\mu_1^N(t),\tilde\mu_j^N(t))]$ is at most $1/(N-1)$ plus the mean disagreement of $\hat X$ and $\tilde X$
-- statement:
--   Let $N\ge2$, let $\mathfrak m^N$ be any initial law, $\gamma^N$ any correlated profile and $u$ any strategy modification, and consider on the canonical $N$-player space the systems $\tilde X$ (Step Two, with player 1 using $u$) and $\hat X$ with the measure $\hat\mu_1(t)=(N-1)^{-1}\sum_{l=2}^N\delta_{\hat X_l(t)}$ of (6.1). Assume $\Psi$ measurable and $f,F$ bounded measurable. Then for every $j\in\{1,\dots,N\}$, including $j=1$, and every $t\in\{0,\dots,T\}$,
--   $$\mathbb E_N\big[\mathrm{dist}\big(\hat\mu_1^N(t),\tilde\mu_j^N(t)\big)\big]\le\frac1{N-1}+\frac1{N-1}\sum_{l=2}^N P_N\big(\hat X_l^N(t)\neq\tilde X_l^N(t)\big).$$
--
--   This is the bridge in the induction proving (6.2): it converts the disagreement of the two systems into closeness of the measures they feed into $\Psi$.
--
--   **Formalization Note** Player 1 is index `0`; $\tilde\mu_j$ is the empirical measure of $\tilde X$ without player $j$.
-- source:
--   Campi & Fischer, Correlated equilibria and mean field games: a simple model, arXiv:2004.06185v2, p. 22, (6.3) (proof of Theorem 6.1, Step Three)

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_Model
import Definitions.Def_SimpleCorrMFG_Conv_NPlayer
import Definitions.Def_SimpleCorrMFG_Conv_Coupling

namespace SimpleCorrMFG.Conv

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

/-- Inequality (6.3) (p. 22): for `N ≥ 2`, every player `j` (including player 1, index `0`) and
every `t`, `E_N[dist(μ̂_1(t), μ̃_j(t))] ≤ 1/(N−1) + (N−1)⁻¹ ∑_{l=2}^N P_N(X̂_l(t) ≠ X̃_l(t))`. -/
theorem eq_6_3 {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MeasurableSpace Γ]
    [DiscreteMeasurableSpace Γ]
    (M : Model T X Γ) (hM : M.Standing) (u : Strat T X Γ → Strat T X Γ)
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (mN : ProbabilityMeasure (Fin N → X))
    (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) (j : Fin N) (t : Fin (T + 1)) :
    ∫ ω, distTV (hatEmp M ω t) (tildeEmp M u ω j t) ∂(nLaw mN γ) ≤
      1 / ((N - 1 : ℕ) : ℝ) + (1 / ((N - 1 : ℕ) : ℝ)) *
        ∑ l ∈ Finset.univ.erase (0 : Fin N),
          (nLaw mN γ).real {ω | hatPath M ω t l ≠ tildePath M u ω t l} := by sorry

end SimpleCorrMFG.Conv
