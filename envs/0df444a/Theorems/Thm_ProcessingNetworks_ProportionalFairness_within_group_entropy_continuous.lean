-- Prove2me | Theorems.Thm_ProcessingNetworks_ProportionalFairness_within_group_entropy_continuous
-- name    : ProcessingNetworks.ProportionalFairness.within_group_entropy_continuous
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:32:44.174107+00:00
-- url     : https://prove2.me/theorems/705f07ee-bdcb-4e12-83ae-277077a15bcb
-- title:
--   Lemma 10.12 — the within-group entropy term is continuous (milestone)
-- statement:
--   **Lemma 10.12.** The function $f : \mathbb R_+ \to \mathbb R$ of Eq. (10.50) is continuous.
--
--   This is the continuity half of showing $\varphi = \sum_\ell \varphi_\ell$ is continuous on
--   $(0,\infty)$ (Lemma 10.7, mission IX), via the alternative expression for $\varphi$ that
--   Section 10.5 develops in terms of the within-group entropy term $f$.
--
--   **Formalization note.** `Z`'s continuity and nonnegativity on $[0,\infty)$ are taken as
--   hypotheses (`hZcont`, `hZnn`): they are established earlier in Section 10.5 as basic properties
--   of any fluid model solution and are not re-derived in this milestone, matching the book's own
--   proof, which invokes them without re-proof at this point.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 199, Lemma 10.12

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_WithinGroupEntropy

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.12, Dai & Harrison p. 199 (PDF p. 215): the within-group entropy term
`withinGroupEntropy` (Eq. 10.50) is continuous on `[0,∞)`, given that `Z` is continuous and
nonnegative there (established earlier in Section 10.5, not re-derived here). -/
theorem within_group_entropy_continuous
    {I L : ℕ} (grp : Fin I → Fin L) (Zh : ℝ → Fin I → ℝ)
    (hZcont : ContinuousOn Zh (Set.Ici 0)) (hZnn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ Zh t i) :
    ContinuousOn (withinGroupEntropy grp Zh) (Set.Ici 0) := by sorry

end ProcessingNetworks.ProportionalFairness
