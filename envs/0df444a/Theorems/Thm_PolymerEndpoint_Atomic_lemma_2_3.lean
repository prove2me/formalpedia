-- Prove2me | Theorems.Thm_PolymerEndpoint_Atomic_lemma_2_3
-- name    : PolymerEndpoint.Atomic.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:06.372912+00:00
-- url     : https://prove2.me/theorems/cf944d05-7f14-4593-bf1b-96f9981bc655
-- title:
--   Lemma 2.3 — triangle inequality for the partitioned distance
-- statement:
--   For any three partitioned subprobability measures $f,g,h$, their distance satisfies
--   $$
--   d(f,h)\leq d(f,g)+d(g,h).
--   $$
--
--   This supplies the triangle inequality for the pseudometric used throughout the compactification.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 20, Lemma 2.3, (2.5)

import Definitions.Def_PolymerEndpoint_Atomic_Partitioned

namespace PolymerEndpoint.Atomic

theorem lemma_2_3 {d : ℕ} (hd : 1 ≤ d) (f g h : PSM d) :
    dist f h ≤ dist f g + dist g h := by sorry

end PolymerEndpoint.Atomic
