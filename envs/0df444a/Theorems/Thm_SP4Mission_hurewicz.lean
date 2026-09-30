-- Prove2me | Theorems.Thm_SP4Mission_hurewicz
-- name    : SP4Mission.hurewicz
-- status  : Open
-- author  : @ryanshin
-- created : 2026-09-09T02:57:39.25877+00:00
-- url     : https://prove2.me/theorems/032e73b7-eda9-4ac9-8445-47583f1c4f7e
-- title:
--   Hurewicz theorem: $\pi_n(X)\cong H_n(X)$ for an $(n-1)$-connected space, $n\ge2$
-- statement:
--   Let $X$ be a topological space (in universe zero) with base point $x$, and let $n\ge2$. Suppose $X$ is $(n-1)$-connected, i.e. $\pi_k(X,x)=0$ for all $0\le k\le n-1$ (so $X$ is path connected and simply connected, with vanishing homotopy groups up to degree $n-1$). Then the $n$-th homotopy group is isomorphic to the $n$-th integral homology group:
--
--   $$
--   \pi_n(X,x)\;\cong\;H_n(X;\mathbb Z).
--   $$
--
--   This is the absolute Hurewicz theorem (Hatcher, Theorem 4.32): for an $(n-1)$-connected space, $n\ge2$, one has $\tilde H_i(X)=0$ for $i<n$ and the Hurewicz homomorphism $h\colon\pi_n(X)\to H_n(X)$, $[f]\mapsto f_*[S^n]$, is an isomorphism. Only the isomorphism clause is stated here, and only as the existence of an isomorphism of abelian groups ($\pi_n$ is abelian for $n\ge2$), which is what the mission needs: in the inductive proof that a simply connected space with vanishing positive-degree homology is weakly contractible, the Hurewicz isomorphism shows that each further homotopy group vanishes.
--
--   **Formalization Note** The theorem is stated with $n$ replaced by $n+2$ so that $n\ge2$ is built in and `HomotopyGroup.Pi (n + 2) X x` carries Mathlib's group structure. Connectivity is `∀ k ≤ n + 1, Subsingleton (HomotopyGroup.Pi k X x)`, homology is `SP4Homology.H (n + 2) X`, and the conclusion is `Nonempty (Additive (π_(n+2) X x) ≃+ H_(n+2)(X))`, an additive group isomorphism between the (additively written) homotopy group and the underlying abelian group of the homology module.
-- source:
--   Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002 (author's edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §4.2, Theorem 4.32, p. 366: "If a space X is (n − 1)-connected, n ≥ 2, then H̃ᵢ(X) = 0 for i < n and πₙ(X) ≈ Hₙ(X)" (absolute case; isomorphism clause).

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy
import Definitions.Def_SP4Homology
import Definitions.Def_SP4HomologyMap

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission CategoryTheory Limits

theorem SP4Mission.hurewicz (n : ℕ) (X : Type) [TopologicalSpace X] (x : X)
    (hconn : ∀ k : ℕ, k ≤ n + 1 → Subsingleton (HomotopyGroup.Pi k X x)) :
    Nonempty (Additive (HomotopyGroup.Pi (n + 2) X x) ≃+ SP4Homology.H (n + 2) X) := by sorry
