-- Prove2me | Theorems.Thm_SP4Mission_weaklyContractible_of_homotopyEquiv
-- name    : SP4Mission.weaklyContractible_of_homotopyEquiv
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-09T02:57:35.034422+00:00
-- url     : https://prove2.me/theorems/98654f2b-d41c-4bd0-8198-486368603265
-- title:
--   Weak contractibility is invariant under homotopy equivalence
-- statement:
--   Let $f\colon X\to Y$ be a homotopy equivalence of topological spaces. If $X$ is weakly contractible — nonempty with $\pi_k(X,x)=0$ for all $k\ge0$ and all base points $x\in X$ — then so is $Y$:
--
--   $$
--   \pi_k(Y,y)=0\qquad\text{for all } k\ge0,\ y\in Y .
--   $$
--
--   This is the homotopy invariance of homotopy groups: a homotopy equivalence induces isomorphisms $\pi_k(X,x)\to\pi_k(Y,f(x))$ for all $k$ and all base points, even when the homotopies are not required to fix base points (Hatcher, p. 342, using the change-of-base-point isomorphisms of §4.1); and since $Y$ is then path connected, every base point $y\in Y$ is reached. In the mission it transports weak contractibility of a manifold to a CW model of the manifold, where Whitehead's theorem applies.
--
--   **Formalization Note** The homotopy equivalence is `ContinuousMap.HomotopyEquiv X Y`; weak contractibility is `SP4WeakHomotopy.WeaklyContractible` (nonempty, and `Subsingleton (HomotopyGroup.Pi k · ·)` for all degrees and base points). The two spaces may live in different universes. Mathlib currently has no induced maps on `HomotopyGroup`, so the statement is a genuine open leaf.
-- source:
--   Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002 (author's edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §4.1, p. 342: "a homotopy equivalence (X, x₀) ≃ (Y, y₀) in the basepointed sense induces isomorphisms on all homotopy groups πₙ. This is true even if basepoints are not required to be stationary during homotopies" (with Proposition 1.18, p. 37, for π₁ and the change-of-basepoint isomorphisms β_h of p. 341 for the general case).

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

theorem SP4Mission.weaklyContractible_of_homotopyEquiv.{u, v}
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (hX : SP4WeakHomotopy.WeaklyContractible X) :
    SP4WeakHomotopy.WeaklyContractible Y := by sorry
