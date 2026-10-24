-- Prove2me | Theorems.Thm_SampleDrivenOS_Limit_lemma_7
-- name    : SampleDrivenOS.Limit.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:35.581633+00:00
-- url     : https://prove2.me/theorems/edeedde7-6117-412b-a770-d421725a34e1
-- title:
--   Lemma 7 — equation (19) has a unique root $\tilde\alpha(p)\in(0,1)$, continuous in $p$
-- statement:
--   For every $p\in(0,1)$ there is exactly one $\tilde\alpha\in(0,1)$ with
--   $$\ln p+\frac{\tilde\alpha(1-p)^2}{p}=\sum_{i=1}^{\infty}\frac{\ln\bigl(1-\tilde\alpha+\tilde\alpha[(i+1)p^i-ip^{i+1}]\bigr)}{i(i+1)} . \qquad(19)$$
--   Furthermore, the map $p\mapsto\tilde\alpha(p)$ is continuous on $(0,1)$.
--
--   $\tilde\alpha(p)$ is the value of the explicit stopping rule of Lemma 6 taken with equality in (18); it is the lower bound in Theorem 8.
--
--   **Formalization Note** The continuity claim is stated for every function $p\mapsto\tilde\alpha(p)$ that picks a root of (19) at each $p\in(0,1)$; by the first part there is exactly one such function on $(0,1)$. The series converges absolutely: each logarithm's argument lies in $[1-\tilde\alpha,1]$.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 17, Lemma 7, (19)

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology

namespace SampleDrivenOS.Limit

/-- Lemma 7 (p. 17): for every `p ∈ (0, 1)` there is a unique `α̃ ∈ (0, 1)` satisfying (19), and
the map `p ↦ α̃(p)` is continuous on `(0, 1)`. -/
theorem lemma_7 :
    (∀ p ∈ Set.Ioo (0:ℝ) 1, ∃! a : ℝ, IsAlphaTilde p a) ∧
      ∀ aT : ℝ → ℝ, (∀ p ∈ Set.Ioo (0:ℝ) 1, IsAlphaTilde p (aT p)) →
        ContinuousOn aT (Set.Ioo 0 1) := by sorry

end SampleDrivenOS.Limit
