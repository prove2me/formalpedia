-- Prove2me | Theorems.Thm_SmaleDiffS4_diffDisk_one_pathConnected
-- name    : SmaleDiffS4.diffDisk_one_pathConnected
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-12T04:25:22.1858+00:00
-- url     : https://prove2.me/theorems/d0287f41-3e87-4ff1-9214-cbbd76325698
-- title:
--   $\mathrm{Diff}(D^1\ \mathrm{rel}\ \partial)$ is path-connected
-- statement:
--   The group $\mathrm{Diff}(D^1\ \mathrm{rel}\ \partial)$ of smooth diffeomorphisms of the line equal to the identity outside the open unit interval is path-connected in the $C^\infty$ topology.
--
--   Such a diffeomorphism $f$ has positive derivative everywhere, since $f'$ never vanishes and equals $1$ outside $(-1,1)$. Hence the straight-line isotopy
--   $$F(t,x)=(1-t)\,x+t\,f(x),\qquad t\in[0,1],$$
--   consists of diffeomorphisms equal to the identity outside $(-1,1)$, and it is a path from the identity to $f$ in the $C^\infty$ topology. This is the one-dimensional case of the question whose four-dimensional case is the mission goal.
--
--   **Formalization Note** `DiffDisk n` is the group of smooth diffeomorphisms of $\mathbb R^n$ equal to the identity at every point of norm $\ge1$, with the $C^\infty$ topology of uniform convergence of all derivatives (published definition `SmaleDiffS4_Basic`). A smooth isotopy is a jointly $C^\infty$ map $F:\mathbb R\times\mathbb R^n\to\mathbb R^n$; only $t\in[0,1]$ matters.
-- source:
--   Classical (the straight-line isotopy shows Diff(D^1 rel ∂) is contractible; cf. S. Smale, "Diffeomorphisms of the 2-sphere", Proc. AMS 10 (1959) for the 2-dimensional case); mission "Smale's question: the homotopy type of Diff(S⁴)"

import Mathlib
import Definitions.Def_SmaleDiffS4_Basic

open SmaleDiffS4
open scoped ContDiff

namespace SmaleDiffS4

/-- **`Diff(D¹ rel ∂)` is path-connected.** Every diffeomorphism of `ℝ` that is the identity
outside the open unit interval is joined to the identity by the straight-line isotopy
`(1 - t) x + t f(x)`, which is a path in the `C^∞` topology. -/
theorem diffDisk_one_pathConnected : PathConnectedSpace (DiffDisk 1) := by
  sorry

end SmaleDiffS4
