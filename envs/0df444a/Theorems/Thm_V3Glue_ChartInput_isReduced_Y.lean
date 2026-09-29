-- Prove2me | Theorems.Thm_V3Glue_ChartInput_isReduced_Y
-- name    : V3Glue.ChartInput.isReduced_Y
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/58f5f145-3945-57f2-9581-e83e19e63804
-- title:
--   Étale charts over a reduced resolution give reduced pieces
-- statement:
--   Let $X$ be a scheme, $N$ a type, and let $C$ be a chart input for $X$ indexed by $N$ in the sense of the project structure [`V3Glue.ChartInput`](def/AlgebraicGeometry_ResolvedModelGlue.html#L291): a family of points $x_n \in X$ with $X_0$ the open subscheme whose points are exactly those distinct from all $x_n$; local models $S_n$ with distinguished opens $V^{\mathrm c}_n \subseteq S_n$; resolutions $\rho_n : \mathrm{Res}_n \to S_n$ which are proper and become isomorphisms after restriction over $V^{\mathrm c}_n$; thickness integers $\ge 1$; opens $U_n \subseteq X$ containing $x_n$ and no other $x_m$, together with étale morphisms $f_n : U_n \to S_n$ meeting $V^{\mathrm c}_n$ exactly away from $x_n$ and satisfying a node condition at $x_n$ (flat stalk map, maximal ideal mapping onto the maximal ideal, isomorphism on residue fields); a base $B$ with $\pi_X : X \to B$ and $\sigma_n : S_n \to B$ making $f_n$ followed by $\sigma_n$ equal to the inclusion of $U_n$ followed by $\pi_X$; flatness of $\rho_n$ followed by $\sigma_n$; local Noetherianity of each $\mathrm{Res}_n$; and the condition that the preimage under $\rho_n$ of the complement of $V^{\mathrm c}_n$ has empty interior. Fix $n : N$ and assume $\mathrm{Res}_n$ is reduced and locally Noetherian. Then the chart's local piece $C.Y\,n$ — the fibre product $U_n \times_{S_n} \mathrm{Res}_n$ — is reduced. (Local Noetherianity of $\mathrm{Res}_n$ is also recorded as a field of the chart data.)
--
--   This is the reducedness half of the integrality statement for the local pieces out of which the resolved model is glued: reducedness descends from the resolution $\mathrm{Res}_n$ of the local model to the chart piece $U_n \times_{S_n} \mathrm{Res}_n$ through the étale chart. It is used in the construction of the resolved Deligne–Rapoport model of the relevant modular curve, where $\mathrm{Res}_n$ is a regular, hence reduced, resolution of the local model $uv = p^e$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_V3Glue_ChartInput_isReduced_Y.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ResolvedModelGlueComponents

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem V3Glue.ChartInput.isReduced_Y {X : Scheme.{0}} {N : Type} (C : V3Glue.ChartInput X N) (n : N)
    [IsReduced (C.Res n)] [IsLocallyNoetherian (C.Res n)] : IsReduced (C.Y n) := by sorry
