-- Prove2me | Theorems.Thm_TwoAssumptions_prop12_poisson_jacobian
-- name    : TwoAssumptions.prop12_poisson_jacobian
-- status  : Open
-- author  : @LG
-- created : 2026-11-22T23:24:11.523887+00:00
-- url     : https://prove2.me/theorems/ae5c8436-ead0-46f0-8274-491c5ea5b59b
-- title:
--   Proposition 12 — the Poisson bracket is the Jacobian of the area transformation
-- statement:
--   **Proposition 12.** The Poisson bracket $\{f,g\}$ translates densities of states into densities per unit area of $f,g$: it is the Jacobian of the transformation $df\,dg\to dq^i\,dp_i$, i.e. $df\,dg=\{f,g\}\,dq^i\,dp_i$.
--
--   For a single degree of freedom $(q,p)$ and two functions $f,g$ of $(q,p)$, the Poisson bracket
--   $$\{f,g\}=\frac{\partial f}{\partial q}\frac{\partial g}{\partial p}-\frac{\partial f}{\partial p}\frac{\partial g}{\partial q}$$
--   equals the determinant of the Jacobian matrix of the map $(q,p)\mapsto(f,g)$.
--
--   **Formalization Note.** Reuses the published canonical Poisson bracket `RelPartMech.poisson` (Definition 11) at $n=1$; the right-hand side is the $2\times2$ determinant (`Matrix.det_fin_two`). The general-$n$ bracket collapses to the $i$-th term when $f,g$ depend only on the $i$-th conjugate pair.
-- source:
--   Cosper 2022, From Two Assumptions to Hamilton's Mechanics, https://github.com/assumptionsofphysics/thesis-ClassicalMechanics, Proposition (12), §2.3; Poisson bracket Definition (11).

import Mathlib
import Definitions.Def_RelPartMech_coordinates
open RelPartMech

namespace TwoAssumptions

theorem prop12_poisson_jacobian (f g : PhaseFn 1) (x p : Coord 1) :
    poisson f g x p =
      (Matrix.of ![![pdq 0 f x p, pdp 0 f x p], ![pdq 0 g x p, pdp 0 g x p]]).det := by sorry

end TwoAssumptions
