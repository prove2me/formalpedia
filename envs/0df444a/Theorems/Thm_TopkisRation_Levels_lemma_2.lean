-- Prove2me | Theorems.Thm_TopkisRation_Levels_lemma_2
-- name    : TopkisRation.Levels.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:14.510447+00:00
-- url     : https://prove2.me/theorems/ab08c9c1-2c18-4935-9ae4-3a1dbd03275a
-- title:
--   Lemma 2, p. 163 — g_t and f_t are convex and continuous on the orthant, and the infimum in (1) is a minimum
-- statement:
--   In the model of Topkis (1968, §1) under Assumptions (A)–(C), let $0\le t\le k$ and let $D=[0,\infty)\times[0,\infty)^n$. Then:
--   1. $g_t(z,b)$ is convex and continuous on $D$;
--   2. if $t\ge1$, $f_t(z,B)$ is convex and continuous on $D$;
--   3. if $t\ge1$, for every $z\ge0$ and $B\ge0$ the infimum in (1) is attained: there is a feasible $u$ with
--   $$
--   f_t(z,B)=p_t\cdot u+h_t\big(z-\mathbf 1\cdot(B-u)\big)+g_{t-1}\big(z-\mathbf 1\cdot(B-u),\,a_tu\big)
--   $$
--   and the bracket of (1) at $u$ is no larger than at any other feasible vector;
--   4. if $t\ge1$, for every $z\ge0$ and $b\ge0$ the function $x\mapsto f_t(z,b+x)$ is integrable with respect to the law $\mu_t$ of $d_t$.
--
--   This is the regularity on which the rest of the analysis rests: the infimum in (1) can be replaced by a minimum, and $g_t$ is a genuine expectation.
--
--   **Formalization Note.** The page writes "$g_t(z,b)$ and $h_t(z,B)$"; the second function is $f_t(z,B)$ (a misprint: $h_t$ has one argument and the next sentence speaks of $f_t$). Item 4 makes explicit what the paper's proof derives from "the Lebesgue Convergence Theorem and the finite means of the demands"; it is what makes the Bochner integral defining $g_t$ the paper's expectation rather than a junk value. Item 3 is the paper's "the infimum can be replaced by minimum", which makes the real `sInf` defining $f_t$ the paper's value.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 163, Lemma 2

import Mathlib
import Definitions.Def_TopkisRation_Levels_Model

namespace TopkisRation.Levels

open MeasureTheory

theorem lemma_2 {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ≤ M.k) :
    (ConvexOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ)) (fun q => M.g t q.1 q.2) ∧
      ContinuousOn (fun q => M.g t q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ))) ∧
    (1 ≤ t →
      ConvexOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ)) (fun q => M.f t q.1 q.2) ∧
      ContinuousOn (fun q => M.f t q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ))) ∧
    (1 ≤ t → ∀ z, 0 ≤ z → ∀ B : Fin n → ℝ, 0 ≤ B →
      ∃ u ∈ feasible z B, M.f t z B = M.obj t (M.g (t - 1)) z B u ∧
        ∀ u' ∈ feasible z B, M.obj t (M.g (t - 1)) z B u ≤ M.obj t (M.g (t - 1)) z B u') ∧
    (1 ≤ t → ∀ z, 0 ≤ z → ∀ b : Fin n → ℝ, 0 ≤ b →
      Integrable (fun x => M.f t z (b + x)) (M.μ t)) := by sorry

end TopkisRation.Levels
