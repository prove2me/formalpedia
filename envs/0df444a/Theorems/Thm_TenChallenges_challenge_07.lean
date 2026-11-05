-- Prove2me | Theorems.Thm_TenChallenges_challenge_07
-- name    : TenChallenges.challenge_07
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T21:20:34.341121+00:00
-- url     : https://prove2.me/theorems/448fe164-14fd-4577-8552-195f8d3b8913
-- title:
--   The sphere-packing constant equals the lattice-packing constant in every dimension
-- statement:
--   **Lattice packings are optimal in every dimension.** For every $r\in\mathbb N$, the sphere-packing constant of $\mathbb R^r$ equals its lattice-packing constant:
--
--   $$\forall r\in\mathbb N:\quad \Delta_r=\Delta_r^L,$$
--
--   where $\Delta_r$ is the supremum of the upper densities of all unit packings of $\mathbb R^r$ and $\Delta_r^L$ the supremum over lattice packings (unit packings that are additive subgroups spanning $\mathbb R^r$). The statement is known for $r\in\{1,2,3,8,24\}$ and open for every other $r\ge 4$; it is a question rather than a conjecture, and in dimension $10$ the densest packing known is not a lattice packing, so the statement may be false.
--
--   **Formalization Note.** The statement is `∀ r, statement_07 r`, an equality in the extended nonnegative reals.
-- source:
--   Open question, see J. H. Conway, N. J. A. Sloane, Sphere Packings, Lattices and Groups, 3rd ed., Chapter 1, Section 1.5 (lattice versus non-lattice packings); scaled form in V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 7

import Definitions.Def_TenChallenges_Challenge_07

namespace TenChallenges
theorem challenge_07 : ∀ r : ℕ, statement_07 r := by sorry
end TenChallenges
