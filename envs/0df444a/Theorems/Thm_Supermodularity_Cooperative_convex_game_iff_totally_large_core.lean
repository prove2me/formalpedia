-- Prove2me | Theorems.Thm_Supermodularity_Cooperative_convex_game_iff_totally_large_core
-- name    : Supermodularity.Cooperative.convex_game_iff_totally_large_core
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:05:00.779992+00:00
-- url     : https://prove2.me/theorems/28efb9ad-8112-43b0-a532-fdbe2167d284
-- title:
--   Theorem 5.2.6 - a game is convex iff its core is totally large
-- statement:
--   A cooperative game is a convex game if and only if it has a totally large core. This is Theorem
--   5.2.6 (p. 220-221), due to Moulin [1990] (sharpening Sharkey [1982a]'s observation that a convex
--   game's core is large): a genuine converse to the "necessity" half already visible in Theorem 5.2.1
--   together with the fact that every subgame of a convex game is again a convex game.
--
--   **Formalization note.** The characteristic function is required throughout the book's chapter to
--   satisfy the standing "cooperative game" hypotheses $f(\emptyset)=0$ and superadditivity
--   (`∀ S1 S2, Disjoint S1 S2 → f S1 + f S2 ≤ f (S1 ∪ S2)`); these are stated as explicit hypotheses
--   here because `IsTotallyLargeCore` alone, without them, does not pin down a cooperative game in the
--   book's sense.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 220-221, Theorem 5.2.6

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_IsConvexGame
import Definitions.Def_Supermodularity_Cooperative_IsTotallyLargeCore

namespace Supermodularity.Cooperative

theorem convex_game_iff_totally_large_core {n : ℕ} (f : Finset (Fin n) → ℝ)
    (hf0 : f ∅ = 0)
    (hsuper : ∀ S1 S2 : Finset (Fin n), Disjoint S1 S2 → f S1 + f S2 ≤ f (S1 ∪ S2)) :
    IsConvexGame f ↔ IsTotallyLargeCore f := by sorry

end Supermodularity.Cooperative
