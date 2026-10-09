-- Prove2me | Theorems.Thm_ReinfRegGames_StrictStable_proposition_C_3_bound
-- name    : ReinfRegGames.StrictStable.proposition_C_3_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:29.260983+00:00
-- url     : https://prove2.me/theorems/0260f583-1bd2-4950-b133-5438444c0388
-- title:
--   Proposition C.3 (first part), p. 35 — F_h(p, y) ≥ ½K ‖Q(y) − p‖² for all y
-- statement:
--   Let $h$ be a $K$-strongly convex penalty function on the simplex $\Delta=\Delta(B)$ (Definition 2.1), with conjugate $h^*(y)=\max_{x\in\Delta}\{\langle y|x\rangle-h(x)\}$ and Fenchel coupling $F_h(p,y)=h(p)+h^*(y)-\langle y|p\rangle$. Let $p\in\Delta$. Then for every score vector $y$ and $x=Q(y)$,
--   $$F_h(p,y)\ \ge\ \tfrac12K\,\|x-p\|_2^2 .$$
--
--   The Fenchel coupling therefore controls the distance of the choice $Q(y)$ from $p$: if $F_h(x^*,y)$ is small, $Q(y)$ is close to $x^*$. This is how the proof of Theorem 5.2 shows that the sublevel set $U^*_\varepsilon$ of $F_h(x^*,\cdot)$ is mapped by $Q$ into a small neighbourhood of $x^*$.
--
--   **Formalization Note** Only the first claim of Proposition C.3 is stated here; the clause "$F_h(p,y)\to0$ iff $Q(y)\to p$" is not part of this item, and (C.11) is a separate item. The norm in the strong convexity inequality (2.5) is the Euclidean one; the page leaves it unspecified, and since $K$ is existential in Definition 2.1 the class of penalty functions does not depend on this choice, but the constant $K$ does.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 35, Proposition C.3, first claim (proof (C.12)–(C.14))

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.StrictStable

theorem proposition_C_3_bound {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : ReinfRegGames.Extinction.IsPenalty h K)
    (p : B → ℝ) (hp : p ∈ stdSimplex ℝ B) (y x : B → ℝ) (hx : ReinfRegGames.Extinction.IsChoice h y x) :
    1 / 2 * K * ReinfRegGames.Extinction.sqDist x p ≤ ReinfRegGames.Extinction.fenchelCoupling h p y := by sorry

end ReinfRegGames.StrictStable
