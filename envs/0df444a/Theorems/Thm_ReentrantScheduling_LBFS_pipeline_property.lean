-- Prove2me | Theorems.Thm_ReentrantScheduling_LBFS_pipeline_property
-- name    : ReentrantScheduling.LBFS.pipeline_property
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:19.30541+00:00
-- url     : https://prove2.me/theorems/ce29bc63-6f1b-4838-af50-b5eac4874aa5
-- title:
--   Pipeline Property of LBFS, p. 1412 — $e(\pi)-\alpha(\pi)\le\overline w x+o(x)$
-- statement:
--   **The Pipeline Property of LBFS.** For every nonacyclic flow line there is a function $g$ with $g(x) = o(x)$ as $x \to \infty$, depending only on the line, such that in every LBFS-admissible run, a released part $\pi$ that finds $x$ other parts in the system satisfies
--
--   $$
--   e(\pi) - \alpha(\pi) \le \overline w\, x + g(x).
--   $$
--
--   Up to a sublinear term, a part's delay under LBFS is the time the bottleneck center needs to process the work the $x$ parts ahead bring to it: the line behaves like a pipeline, as an acyclic line does. Whether $o(x)$ can be replaced by $O(1)$ is stated as open on the same page.
--
--   **Formalization Note.** $g$ is chosen before the run and is the same for all runs and parts of the line. $o(x)$ is `Asymptotics.IsLittleO` at `atTop` against the identity on $\mathbb R$.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1412, The Pipeline Property of LBFS

import Mathlib
import Definitions.Def_ReentrantScheduling_LBFS_Model
import Definitions.Def_ReentrantScheduling_LBFS_Constants

namespace ReentrantScheduling.LBFS

/-- The Pipeline Property of LBFS, p. 1412: there is a function `g = o(x)`, depending only on the
line, such that under LBFS every released part `π` that finds `x` other parts in the system
satisfies `e(π) − α(π) ≤ w̄ x + g(x)`. -/
theorem pipeline_property (L : Line) :
    ∃ g : ℝ → ℝ, g =o[Filter.atTop] (fun y : ℝ => y) ∧
      ∀ R : Run L, R.Admissible L.lbfsPrio → ∀ π : R.Part, ¬ R.initial π →
        ∀ x : ℕ, (R.othersAtArrival π).encard = x →
          R.exit π ≤ ((R.α π + L.wbar * x + g x : ℝ) : WithTop ℝ) := by sorry

end ReentrantScheduling.LBFS
