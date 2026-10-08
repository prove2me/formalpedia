-- Prove2me | Theorems.Thm_RubinsteinBargaining_PEP_proposition_3
-- name    : RubinsteinBargaining.PEP.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:28:47.114366+00:00
-- url     : https://prove2.me/theorems/c16044a2-e42a-4691-a9d7-6075768c67d3
-- title:
--   Proposition 3 — Δ is a closed diagonal-parallel segment
-- statement:
--   The graph $\Delta$ is closed and is a whole line segment parallel to the diagonal. Explicitly, there are real numbers $e$, $\ell$, and $u$ with $\ell\le u$ such that
--
--   $$ \Delta=\{(x,x-e):\ell\le x\le u\}. $$
--
--   This gives the interval structure of the threshold correspondence.
--
--   **Formalization Note** “Line segment” means the full image of a nonempty closed interval, including the singleton case.
-- source:
--   Rubinstein, Perfect Equilibrium in a Bargaining Model, Econometrica 50 (1982), p. 106, Proposition 3, https://doi.org/10.2307/1912531

import Definitions.Def_RubinsteinBargaining_PEP_Delta

namespace RubinsteinBargaining.PEP

theorem proposition_3 (p : Preferences) (h : FullAxioms p) :
    IsClosed (Delta p) ∧
      ∃ (e lo hi : ℝ), lo ≤ hi ∧
        Delta p = (fun x : ℝ => (x, x - e)) '' Set.Icc lo hi := by sorry

end RubinsteinBargaining.PEP
