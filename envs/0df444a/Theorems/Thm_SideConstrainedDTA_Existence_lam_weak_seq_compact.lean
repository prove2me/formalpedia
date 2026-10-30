-- Prove2me | Theorems.Thm_SideConstrainedDTA_Existence_lam_weak_seq_compact
-- name    : SideConstrainedDTA.Existence.lam_weak_seq_compact
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-29T23:32:43.556762+00:00
-- url     : https://prove2.me/theorems/cccb2826-22d5-4fbe-9851-4535f36fb012
-- title:
--   Λ(Q) is weakly sequentially compact in L²([t0,tf])^P (proof of Theorem 7.6, p. 40)
-- statement:
--   Let $\Lambda(Q)$ be the set of walk inflows with departure time choice: measurable $h=(h_p)_{p\in\mathcal P}$ with $0\le h_p\le B_p$ almost everywhere on $[t_0,t_f]$, $h_p=0$ almost everywhere outside $[t_0,t_f]$, and $\sum_{p\in\mathcal P_i}\int_{t_0}^{t_f}h_p(t)\,dt=Q_i$ for every commodity $i$.
--
--   Then every sequence $(h^n)_{n\in\mathbb N}\subseteq\Lambda(Q)$ has a subsequence $(h^{n_k})_k$ and a limit $h^*\in\Lambda(Q)$ such that $h^{n_k}\rightharpoonup h^*$ weakly in $L^2([t_0,t_f])^{\mathcal P}$, i.e.
--   $$
--   \sum_{p\in\mathcal P}\int_{t_0}^{t_f} g_p(t)\,h^{n_k}_p(t)\,dt\;\longrightarrow\;\sum_{p\in\mathcal P}\int_{t_0}^{t_f} g_p(t)\,h^{*}_p(t)\,dt\qquad(k\to\infty)
--   $$
--   for every $g\in L^2([t_0,t_f])^{\mathcal P}$.
--
--   This is the compactness step used in the proof of Theorem 7.6 ("By taking subsequences, $h^n$ weakly converges to some $h^*\in\Lambda$ as $\Lambda$ is bounded, closed and convex"), and it is needed in the same way whenever an equilibrium is obtained as a weak limit of approximate equilibria, e.g. for the uniform bound in Claim 5.
--
--   **Formalization Note.** The subsequence is given by a strictly increasing index map $\varphi:\mathbb N\to\mathbb N$; weak convergence is `WeakTendsto` from the setting file (tested against all $g$ whose components are in $L^2$ on $[t_0,t_f]$). The limit is a genuine pointwise-defined, measurable representative satisfying all conditions of `Lam`.
-- source:
--   Graf, Harks, Side-Constrained Dynamic Traffic Equilibria, arXiv:2211.03194v3, p. 40, proof of Theorem 7.6 ("By taking subsequences, h^n weakly converges to some h* in Λ as Λ is bounded, closed and convex (cf. [Hun13, Corollary 7.32])"); Λ(Q) as defined on p. 10

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting

open MeasureTheory Set Filter Topology

namespace SideConstrainedDTA.Existence

/-- p. 40 (cf. [Hun13, Corollary 7.32]): `Λ(Q)` is weakly sequentially compact — every sequence
in `Λ(Q)` has a subsequence converging weakly in `L²([t0, tf])^P` to some limit in `Λ(Q)`. -/
theorem lam_weak_seq_compact {I W E : Type*} [Fintype W] [DecidableEq I]
    (N : Model I W E) (hs : ℕ → W → ℝ → ℝ) (hhs : ∀ n, Lam N (hs n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ hstar : W → ℝ → ℝ, Lam N hstar ∧
      WeakTendsto N (fun n => hs (φ n)) hstar := by sorry

end SideConstrainedDTA.Existence
