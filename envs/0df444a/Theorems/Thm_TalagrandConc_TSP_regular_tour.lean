-- Prove2me | Theorems.Thm_TalagrandConc_TSP_regular_tour
-- name    : TalagrandConc.TSP.regular_tour
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:38.295988+00:00
-- url     : https://prove2.me/theorems/20330dae-6edf-4b52-a86e-7c7841714b43
-- title:
--   Lemma 11.2.1 — local regularity of shortest Euclidean tours
-- statement:
--   There is a universal constant $K>0$ with the following property. Let $F$ be a finite set in $[0,1]^2$, let $C$ be a level-$k$ dyadic square with $k\ge1$, and let $G$ be a finite subset of $C$. If some point of $F$ is within Euclidean distance $2^{-k+2}$ of $C$, then the shortest closed tour length satisfies
--   $$T(F)\le T(F\cup G)\le T(F)+K2^{-k}\sqrt{|G|}.$$
--
--   This is the local regularity condition that lets the concentration theorem apply to the traveling salesman tour length.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 175, Lemma 11.2.1, Eq. (11.2.1)

import Mathlib
import Definitions.Def_TalagrandConc_TSP_Basic

namespace TalagrandConc.TSP

/-- Talagrand (1995), Lemma 11.2.1, p. 175. -/
theorem regular_tour : ∃ K : ℝ, 0 < K ∧ Regular K tourLength := by sorry

end TalagrandConc.TSP
