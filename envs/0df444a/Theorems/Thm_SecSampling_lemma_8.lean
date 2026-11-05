-- Prove2me | Theorems.Thm_SecSampling_lemma_8
-- name    : SecSampling.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:51.313493+00:00
-- url     : https://prove2.me/theorems/35aafcf9-8009-4a81-953d-c905b85bcb72
-- title:
--   Lemma 8 — conflict iff linked by a monotone path
-- statement:
--   Let $I_1,I_2$ be bit strings. Then $I_1$ and $I_2$ (with $I_1$ the shorter) are in conflict if and only if there is a monotone path in the conflict graph that starts at $I_1$ and ends at $I_2$.
--
--   Consequently the conflict relation is the ancestor–descendant relation of the conflict graph, which is what allows the paper to reason about strategies node by node.
--
--   Differences from the source:
--   - reading: two instances are in conflict iff they are linked by a monotone path → Conflict I₁ I₂ (I₁ the shorter) iff some monotone path with at least two nodes runs from I₁ to I₂; reason: conflict is defined for an ordered pair with n₁ < n₂ (p.15), so the path has distinct ends and runs from the shorter instance
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, Lemma 8, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_SecSampling_ConflictGraph

namespace SecSampling

/-- **Lemma 8** (arXiv:2011.07869v1, p.15). Two instances are in conflict if and only if they are
linked by a monotone path in the conflict graph: `I₁` (the shorter) conflicts with `I₂` iff some
monotone path starts at `I₁` and ends at `I₂`. -/
theorem lemma_8 (I₁ I₂ : List Bool) :
    Conflict I₁ I₂ ↔ ∃ P : List (List Bool), IsMonotonePath (I₁ :: (P ++ [I₂])) := by sorry

end SecSampling
