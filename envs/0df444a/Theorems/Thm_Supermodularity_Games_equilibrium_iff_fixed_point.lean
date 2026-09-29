-- Prove2me | Theorems.Thm_Supermodularity_Games_equilibrium_iff_fixed_point
-- name    : Supermodularity.Games.equilibrium_iff_fixed_point
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-18T05:31:52.501976+00:00
-- url     : https://prove2.me/theorems/c5f54347-ed94-49e7-8dbb-79854daa8e24
-- title:
--   Lemma 4.2.1 - equilibrium points are the fixed points of the best joint response
-- statement:
--   With $S$ and $f$ as in `BestResponse`, for every feasible joint strategy $x'$:
--   $$
--   x' \text{ is an equilibrium point} \quad\Longleftrightarrow\quad x' \in Y(x'),
--   $$
--   where $Y$ is the best joint response correspondence. This is Lemma 4.2.1: the set of
--   all equilibrium points for a noncooperative game is identical to the set of fixed
--   points of $Y$. It reduces the search for an equilibrium point to a fixed-point
--   problem, which is what lets the lattice fixed-point machinery of chunk `01-lattices`
--   (Theorem 2.5.1) apply to games at all.
--
--   **Formalization Note** Stated as a biconditional at a single joint strategy `x'`,
--   matching the book's "the set of equilibrium points is identical to the set of fixed
--   points" as an extensional set equality unfolded pointwise.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 179-180, Lemma 4.2.1

import Mathlib
import Definitions.Def_Supermodularity_Games_IsEquilibrium
import Definitions.Def_Supermodularity_Games_BestJointResponse

namespace Supermodularity.Games

theorem equilibrium_iff_fixed_point {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (x' : ∀ i, Fin (m i) → ℝ) :
    IsEquilibrium S f x' ↔ x' ∈ BestJointResponse S f x' := by sorry

end Supermodularity.Games
