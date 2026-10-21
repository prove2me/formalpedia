-- Prove2me | Theorems.Thm_PBElicit_RandThresh_theorem_3_5
-- name    : PBElicit.RandThresh.theorem_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:27.892652+00:00
-- url     : https://prove2.me/theorems/1f8f9556-8a1b-462b-b30c-891657fd9e09
-- title:
--   Theorem 3.5, p. 12 — the distortion associated with randomized threshold approval votes is O(log² m)
-- statement:
--   In participatory budgeting with $n$ voters, a set $A$ of $m$ alternatives with costs $c_a\in[0,1]$ and budget $1$, voters hold nonnegative additive utilities normalized to $v_i(A)=1$, but report only **threshold approval votes**: at a threshold $t$, voter $i$ reports the set $\{a: v_i(a)\ge t\}$. A randomized rule draws the threshold and then aggregates the reported profile into an inclusion-maximal budget-feasible set.
--
--   **Theorem 3.5.** The distortion associated with randomized threshold approval votes is $O(\log^2 m)$: there is an absolute constant $C>0$ such that for every $n$, every $A$ with $m\ge 2$ and every cost vector $c\in[0,1]^A$, some randomized threshold rule $R$ satisfies, for every normalized utility profile $\vec v$,
--   $$
--   \max_{T\in\mathcal F_c}\mathrm{sw}(T,\vec v)\ \le\ C\log^2 m\cdot\mathbb E[\mathrm{sw}(R,\vec v)].
--   $$
--
--   By Observation 3.1 the trivial rule achieves distortion $m$, and deterministic thresholds cannot beat $\Omega(\sqrt m)$ (Theorem 3.4), so randomizing the threshold gives an exponential improvement.
--
--   **Formalization Note.**
--   1. *Distortion.* The page defines $\mathrm{dist}(f)=\sup_{\vec v}\mathbb E_{t\sim D}\,\max_T\mathrm{sw}(T,\vec v)/\mathbb E[\mathrm{sw}(f(\vec\rho(\vec v,t)),\vec v)]$, with $\mathbb E_t$ in front of the ratio. The proof bounds the total expected welfare instead ("its expected social welfare is at least $\mathrm{sw}(S^*,\vec v)/(2+16\log^2m)$"), so the Lean states $\mathrm{OPT}\le C\log^2m\cdot\mathbb E_{t}\mathbb E[\mathrm{sw}]$, multiplicatively. By Jensen's inequality ($x\mapsto 1/x$ is convex) the printed quantity is at least $\mathrm{OPT}/\mathbb E_t\mathbb E[\mathrm{sw}]$, so the printed definition is the more demanding one; the Lean states the form the paper's proof establishes.
--   2. *Distortion associated with a format* is the distortion of the best rule, so the statement is existential: some rule, fixed before the utilities (∃ rule ∀ profile), may depend on $n$, $A$ and $c$. Rules are finite mixtures of (threshold, deterministic aggregation of the approval profile into $\mathcal F_c$).
--   3. Costs lie in $[0,1]$ (each single project is affordable, as the paper's proofs use). $m\ge 2$ excludes $m=1$, where $\log^2 m=0$. $\log$ is $\log_2$. The bound is claimed for every $m\ge 2$, not only powers of $2$ (the page's "assume $m$ is a power of 2" is an expository simplification).
--   4. The constant $C$ is absolute: it is chosen before $n$, $A$ and $c$.
-- source:
--   Benadè, Nath, Procaccia & Shah, Preference Elicitation for Participatory Budgeting, author's manuscript (2018; Manag. Sci. 2021, doi:10.1287/mnsc.2020.3666), Theorem 3.5, p. 12 (distortion of randomized threshold rules, §3.1.3, p. 12)

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting

namespace PBElicit.RandThresh

theorem theorem_3_5 : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] (c : A → ℝ),
      (∀ a, 0 ≤ c a ∧ c a ≤ 1) → 2 ≤ Fintype.card A →
      ∃ R : ThresholdRule n A c, ∀ v : Fin n → A → ℝ, IsUtilityProfile v →
        ∀ T : Finset A, IsMaxFeasible c T →
          sw v T ≤ C * Real.logb 2 (Fintype.card A) ^ 2 * R.expWelfare v := by sorry

end PBElicit.RandThresh
