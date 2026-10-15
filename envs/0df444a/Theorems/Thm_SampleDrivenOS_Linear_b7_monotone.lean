-- Prove2me | Theorems.Thm_SampleDrivenOS_Linear_b7_monotone
-- name    : SampleDrivenOS.Linear.b7_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:22.271782+00:00
-- url     : https://prove2.me/theorems/ff3cd208-40a1-41d0-8110-063390e1d9dd
-- title:
--   B.7, p. 34 — $f(p,\alpha)$ is increasing and $g(p,\alpha)$ is decreasing in $\alpha$
-- statement:
--   Fix $p\in(0,1)$ and let
--   $$f(p,\alpha)=\ln p+\frac{\alpha(1-p)^2}{p},\qquad g(p,\alpha)=\sum_{i=1}^{\infty}\frac{\ln\bigl(1+\alpha(p^i(1+i(1-p))-1)\bigr)}{i(i+1)}$$
--   be the two sides of equation (19). Then
--
--   1. $\alpha\mapsto f(p,\alpha)$ is strictly increasing on $[0,1]$;
--   2. $\alpha\mapsto g(p,\alpha)$ is non-increasing on $[0,1)$.
--
--   Together they give the uniqueness of the root $\tilde\alpha(p)$ of (19) (Lemma 7), and after the substitution $\alpha=f(p)\,p$ they are the monotonicity used in the first step of the proof of Theorem 9.
--
--   **Formalization Note** The paper's sentences say "increasing" and "decreasing" without naming the domain. Strictness is stated for $f$ (its slope $(1-p)^2/p$ is positive); $g$ is stated as non-increasing on $[0,1)$, where every logarithm's argument is at least $1-\alpha>0$; at $\alpha=1$ the paper itself notes $g(p,1)=-\infty$, so $\alpha=1$ is excluded. The continuity claim of the same paragraph is used only for Lemma 7 and is not part of this statement.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 34, B.7 (Proof of Lemma 7), first paragraph

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

namespace SampleDrivenOS.Linear

theorem b7_monotone (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    StrictMonoOn (fB7 p) (Set.Icc 0 1) ∧ AntitoneOn (gB7 p) (Set.Ico 0 1) := by sorry

end SampleDrivenOS.Linear
