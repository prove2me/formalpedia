-- Prove2me | Theorems.Thm_SimpleCorrMFG_Conv_eq_6_2
-- name    : SimpleCorrMFG.Conv.eq_6_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:39.648644+00:00
-- url     : https://prove2.me/theorems/13d15d2f-ba83-4e9e-be72-5089ac3e8dc5
-- title:
--   (6.2), p. 22 — the decoupled system $\hat X$ and the system $\tilde X$ agree for most players as $N\to\infty$
-- statement:
--   Assume that $\Psi$ is measurable, $f,F$ bounded measurable, and that the first part of (A1) holds. Fix a strategy modification $u$, an arbitrary sequence of initial laws $\mathfrak m^N\in\mathcal P(\mathcal X^N)$ and correlated profiles $\gamma^N\in\mathcal P(\mathcal R^N)$, $N\ge2$, and consider on the canonical $N$-player spaces the systems $\tilde X^N$ (Step Two) and $\hat X^N$ (Step Three). Then for every $t\in\{0,\dots,T\}$,
--   $$\frac1{N-1}\sum_{j=2}^N P_N\big(\hat X_j^N(t)\neq\tilde X_j^N(t)\big)\xrightarrow[N\to\infty]{}0.$$
--
--   The claim shows that removing player 1 (and its deviation $u$) from the empirical measure does not affect the other players in the limit; it is the key step in proving that the flow of measures in the limit is unaffected by a unilateral deviation.
--
--   **Formalization Note** The sequence is indexed by $n$ with $N=n+2$. No symmetry, equilibrium property or product structure of $\mathfrak m^N$ is assumed: the paper's argument does not use them. The paper's text uses only that $w$ is bounded with $w(s)\to0$ as $s\to0^+$; since (A1) does not require $w(0)=0$, the step "$\mathbb E[w(\mathrm{dist})]\to0$" needs the observation that the indicator vanishes when $\mathrm{dist}=0$.
-- source:
--   Campi & Fischer, Correlated equilibria and mean field games: a simple model, arXiv:2004.06185v2, p. 22, (6.2) (proof of Theorem 6.1, Step Three)

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_Model
import Definitions.Def_SimpleCorrMFG_Conv_NPlayer
import Definitions.Def_SimpleCorrMFG_Conv_Coupling

namespace SimpleCorrMFG.Conv

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

/-- Claim (6.2) (p. 22): under the first part of (A1), for every strategy modification `u`, every
sequence of initial laws and correlated profiles, and every `t`,
`(N−1)⁻¹ ∑_{j=2}^N P_N(X̂_j(t) ≠ X̃_j(t)) → 0` as `N → ∞`. The `n`-th term is the game with
`N = n + 2` players. -/
theorem eq_6_2 {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MeasurableSpace Γ]
    [DiscreteMeasurableSpace Γ]
    (M : Model T X Γ) (hM : M.Standing) (hA1a : M.A1a) (u : Strat T X Γ → Strat T X Γ)
    (mN : (n : ℕ) → ProbabilityMeasure (Fin (n + 2) → X))
    (γ : (n : ℕ) → ProbabilityMeasure (Fin (n + 2) → Strat T X Γ)) (t : Fin (T + 1)) :
    Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ j ∈ Finset.univ.erase (0 : Fin (n + 2)),
          (nLaw (mN n) (γ n)).real {ω | hatPath M ω t j ≠ tildePath M u ω t j})
      atTop (𝓝 0) := by sorry

end SimpleCorrMFG.Conv
