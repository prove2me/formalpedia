-- Prove2me | Theorems.Thm_RestrictedAssignment_Svensson_dual_objective_neg_of_no_potential_move
-- name    : RestrictedAssignment.Svensson.dual_objective_neg_of_no_potential_move
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:29:07.573055+00:00
-- url     : https://prove2.me/theorems/04d9e45e-66aa-46e9-8068-804366b6f99a
-- title:
--   Claim 4.8 — with no potential move, $\sum_i y^*_i < \sum_j z^*_j$
-- statement:
--   Let $(J, M, p, \Gamma)$ be an instance of restricted assignment with $p_j \ge 0$ for all $j$, let $\sigma_0$ be a valid partial schedule and $j_{\mathrm{new}}$ a job with $\sigma_0(j_{\mathrm{new}}) = \mathrm{TBD}$ and $\Gamma(j_{\mathrm{new}}) \neq \emptyset$. Let $(\sigma, T)$ be a state reached by Algorithm 2 on $(\sigma_0, j_{\mathrm{new}})$ in which $\sigma(j_{\mathrm{new}})$ is still TBD and no potential move is available. Then
--   $$
--   \sum_{i \in M} y^*_i \;<\; \sum_{j \in J} z^*_j .
--   $$
--
--   With Claim 4.7 and the dual certificate, this gives Lemma 4.6.
--
--   **Formalization Note** The hypothesis $\Gamma(j_{\mathrm{new}}) \neq \emptyset$ is not in the printed claim. Without it the claim fails: if $p(j_{\mathrm{new}}) = 0$ and $\Gamma(j_{\mathrm{new}}) = \emptyset$, the initial state has no potential move and both sides are equal. The hypothesis is implied by feasibility of [C-LP], which is the setting of Lemma 4.6 where the claim is used.
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, p. 17, Claim 4.8 (proof pp. 17-19)

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP
import Definitions.Def_RestrictedAssignment_Svensson_extendSchedule

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 17, Claim 4.8: in an iteration of Algorithm 2 in which no
potential move is available, `∑_i y*_i < ∑_j z*_j`. The hypothesis `Γ(j_new) ≠ ∅` is added:
without it the claim fails for a job `j_new` of size 0 with no admissible machine. -/
theorem dual_objective_neg_of_no_potential_move {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (σ0 : J → Option M) (jnew : J)
    (hσ0 : Valid Γ p σ0) (hjnew : σ0 jnew = none) (hΓnew : (Γ jnew).Nonempty)
    (s : AlgState J M) (hs : Reachable Γ p σ0 jnew s) (hloop : s.σ jnew = none)
    (hnone : ∀ j i, ¬ IsPotentialMove Γ p s j i) :
    ∑ i, yStar Γ p s i < ∑ j, zStar Γ p s j := by sorry

end RestrictedAssignment.Svensson
