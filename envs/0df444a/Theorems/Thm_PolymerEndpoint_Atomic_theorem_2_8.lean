-- Prove2me | Theorems.Thm_PolymerEndpoint_Atomic_theorem_2_8
-- name    : PolymerEndpoint.Atomic.theorem_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:58.55449+00:00
-- url     : https://prove2.me/theorems/e2d0106a-0576-48fe-800d-6c04f9a7843c
-- title:
--   Theorem 2.8 — sequential compactness
-- statement:
--   Every sequence $(f_n)$ of partitioned subprobability measures has a subsequence converging in the partitioned distance to another such measure $g$:
--   $$
--   d(f_{n_k},g)\longrightarrow0.
--   $$
--
--   This gives the compactness needed to extract limits of empirical endpoint laws. The convergence is in the paper's quotient pseudometric, so representatives need only converge to distance zero.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 24, Theorem 2.8

import Definitions.Def_PolymerEndpoint_Atomic_Partitioned

open Filter
open scoped Topology

namespace PolymerEndpoint.Atomic

theorem theorem_2_8 {d : ℕ} (hd : 1 ≤ d) (f : ℕ → PSM d) :
    ∃ g : PSM d, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => dist (f (φ k)) g) atTop (𝓝 0) := by sorry

end PolymerEndpoint.Atomic
