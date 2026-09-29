-- Prove2me | Theorems.Thm_RestrictedAssignment_Svensson_extendSchedule_terminates
-- name    : RestrictedAssignment.Svensson.extendSchedule_terminates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:30:20.082832+00:00
-- url     : https://prove2.me/theorems/368fee6f-6e56-4bad-a9e8-4531a4ed404b
-- title:
--   Lemma 4.9 — Algorithm 2 terminates (positive job sizes)
-- statement:
--   Let $(J, M, p, \Gamma)$ be an instance of restricted assignment in which every job has positive size, $p_j > 0$. Let $\sigma_0$ be a valid partial schedule and $j_{\mathrm{new}}$ a job with $\sigma_0(j_{\mathrm{new}}) = \mathrm{TBD}$. Then Algorithm 2 started on $(\sigma_0, j_{\mathrm{new}})$ has no infinite run: there is no sequence of states $s_0, s_1, s_2, \dots$ with $s_0$ the initial state and $s_{n+1}$ obtained from $s_n$ by one iteration of the while loop, whichever potential move of minimum value is chosen in each iteration.
--
--   In particular, if there is always a potential move to choose, Algorithm 2 terminates, i.e. assigns $j_{\mathrm{new}}$. Combined with Lemma 4.6, this is the correctness of the local search.
--
--   **Formalization Note** The printed lemma allows $p_j \ge 0$. Its proof uses that moving a job off a machine in a small blocker strictly decreases that machine's load, which fails for a job of size $0$, and the statement fails too. Take one small job $j_{\mathrm{new}}$ of size $9/17$ with $\Gamma(j_{\mathrm{new}}) = \{a, b\}$, a job $z$ of size $0$ with $\Gamma(z) = \{a,b\}$, a job of size $25/17$ with $\Gamma = \{a\}$ on $a$, a job of size $25/17$ with $\Gamma = \{b\}$ on $b$, and $z$ on $a$. Then the algorithm can alternate forever between blocking $a$, moving $z$ to $b$, blocking $b$ and moving $z$ back to $a$, with all choices of minimum value. The hypothesis $p_j > 0$ excludes this and loses nothing for the goal, where jobs of size $0$ can be placed at the end.
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, p. 19, Lemma 4.9 (proof pp. 19-20)

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP
import Definitions.Def_RestrictedAssignment_Svensson_extendSchedule

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 19, Lemma 4.9: Algorithm 2 terminates — it has no infinite
run, whatever potential move of minimum value is chosen in each iteration. Stated for positive
job sizes: with a job of size 0 the printed statement fails (see the natural-language
statement). -/
theorem extendSchedule_terminates {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (σ0 : J → Option M) (jnew : J) (hσ0 : Valid Γ p σ0) (hjnew : σ0 jnew = none) :
    ¬ ∃ f : ℕ → AlgState J M,
        f 0 = initState σ0 jnew ∧ ∀ n, Step Γ p jnew (f n) (f (n + 1)) := by sorry

end RestrictedAssignment.Svensson
