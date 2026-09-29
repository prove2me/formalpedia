-- Prove2me | Theorems.Thm_RestrictedAssignment_Svensson_configLP_integrality_gap
-- name    : RestrictedAssignment.Svensson.configLP_integrality_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:32:28.982171+00:00
-- url     : https://prove2.me/theorems/f83dc63c-d76c-4bb4-ba6f-04234a1f347d
-- title:
--   Theorem 4.1 — the configuration LP of restricted assignment has integrality gap at most 33/17
-- statement:
--   Let $J$ be a finite set of jobs and $M$ a finite set of machines, let each job $j$ have size $p_j \ge 0$ and a set $\Gamma(j) \subseteq M$ of machines it may be assigned to. Let $T \ge 0$. If the configuration LP [C-LP] is feasible for target makespan $T$, then there is a schedule $\sigma : J \to M$ with $\sigma(j) \in \Gamma(j)$ for every job $j$ whose makespan is at most $\tfrac{33}{17}\,T$:
--   $$
--   \sum_{j :\, \sigma(j) = i} p_j \;\le\; \frac{33}{17}\, T \qquad \text{for every machine } i \in M .
--   $$
--
--   Taking $T = \mathrm{OPT}_{LP}$, the optimal makespan satisfies $\mathrm{OPT} \le \tfrac{33}{17}\,\mathrm{OPT}_{LP}$; since $\mathrm{OPT}_{LP} \le \mathrm{OPT}$, the configuration LP gives an estimate of the optimal makespan of restricted assignment within a factor $33/17 \approx 1.9412$, strictly better than $2$.
--
--   **Formalization Note** The statement is scale-free and does not define $\mathrm{OPT}_{LP}$; it is equivalent to the paper's form under the normalization $\mathrm{OPT}_{LP} = 1$. The hypothesis $T \ge 0$ is needed: with no jobs and $T < 0$, [C-LP] is feasible while every load is $0 > \tfrac{33}{17} T$.
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, p. 11, Theorem 4.1

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 11, Theorem 4.1: the [C-LP] has integrality gap at most
33/17. Stated scale-free: if [C-LP] is feasible for a target makespan `T ≥ 0`, there is a
schedule respecting `Γ` of makespan at most `(33/17) T`. -/
theorem configLP_integrality_gap {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (T : ℝ) (hT : 0 ≤ T)
    (hLP : CLPFeasible Γ p T) :
    ∃ σ : J → M, (∀ j, σ j ∈ Γ j) ∧ ∀ i, schedLoad p σ i ≤ 33 / 17 * T := by sorry

end RestrictedAssignment.Svensson
