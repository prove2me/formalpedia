-- Prove2me | Theorems.Thm_SchrijverSFM_Alg_subroutine_exists
-- name    : SchrijverSFM.Alg.subroutine_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:49.9063+00:00
-- url     : https://prove2.me/theorems/b7d423ed-0cc4-47dd-8d41-4dcffd1deb85
-- title:
--   Display (12), §3, p. 350 — h^≺ + δ(χ^t − χ^s) is a convex combination of the h^{≺^{s,u}}, u ∈ (s, t]_≺, for some δ ≥ 0
-- statement:
--   Let $f$ be a submodular real function on the subsets of $V = \{0, \dots, n-1\}$, let $\prec$ be a total order on $V$, and let $s, t \in V$ with $s \prec t$. For each $u \in (s,t]_\prec = \{v \mid s \prec v \preceq t\}$ let $\prec^{s,u}$ be the order obtained from $\prec$ by moving $u$ to the position just before $s$. Then there are $\delta \ge 0$ and weights $\mu_u \ge 0$ ($u \in (s,t]_\prec$) with $\sum_{u \in (s,t]_\prec} \mu_u = 1$ such that
--   $$h^\prec + \delta(\chi^t - \chi^s) = \sum_{u \in (s,t]_\prec} \mu_u\, h^{\prec^{s,u}},$$
--   where $\chi^u$ is the incidence vector of $u$.
--
--   This is the subroutine of the algorithm: it moves a nonnegative amount of weight from coordinate $s$ to coordinate $t$ while replacing $\prec$ by orders with shorter intervals $(s, t]$.
--
--   **Formalization Note** Only the existence part of (12) is stated; "in strongly polynomial time" is not formalized (there is no machine model). The family of moved orders is given as a function $u \mapsto \tau_u$ satisfying `IsMoved σ s u τ_u` for each $u$ in the interval, and $\mu$ is a function on $V$ whose values outside the interval are irrelevant. The normalization $f(\emptyset) = 0$ is not needed and is not assumed.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), p. 350, display (12)

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting

namespace SchrijverSFM.Alg

open NonmonotoneSubmod.Shared

theorem subroutine_exists {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (σ : Equiv.Perm (Fin n)) (s t : Fin n) (hst : σ s < σ t)
    (τ : Fin n → Equiv.Perm (Fin n)) (hτ : ∀ u ∈ interval σ s t, IsMoved σ s u (τ u)) :
    ∃ δ : ℝ, 0 ≤ δ ∧ ∃ μ : Fin n → ℝ, (∀ u, 0 ≤ μ u) ∧ (∑ u ∈ interval σ s t, μ u) = 1 ∧
      ∀ v : Fin n, greedy f σ v + δ * (chi t v - chi s v) =
        ∑ u ∈ interval σ s t, μ u * greedy f (τ u) v := by sorry
end SchrijverSFM.Alg
