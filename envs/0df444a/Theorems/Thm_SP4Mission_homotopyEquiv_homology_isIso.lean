-- Prove2me | Theorems.Thm_SP4Mission_homotopyEquiv_homology_isIso
-- name    : SP4Mission.homotopyEquiv_homology_isIso
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-09T02:57:32.66844+00:00
-- url     : https://prove2.me/theorems/795ae855-f067-40d5-aac6-34c2a2116eff
-- title:
--   A homotopy equivalence induces isomorphisms on integral singular homology
-- statement:
--   Let $X$ and $Y$ be topological spaces (in universe zero) and let $f\colon X\to Y$ be a homotopy equivalence, with homotopy inverse $g\colon Y\to X$ (so $g\circ f\simeq\mathrm{id}_X$ and $f\circ g\simeq\mathrm{id}_Y$). Then for every $k\ge0$ the induced map
--
--   $$
--   f_*\colon H_k(X;\mathbb Z)\xrightarrow{\ \cong\ }H_k(Y;\mathbb Z)
--   $$
--
--   is an isomorphism. This is the homotopy invariance of singular homology in its most used form: homotopic maps induce the same homomorphism on homology, so $g_*f_*=(g\circ f)_*=(\mathrm{id}_X)_*=\mathrm{id}$ and likewise $f_*g_*=\mathrm{id}$, whence $f_*$ is invertible with inverse $g_*$. In the mission it is used to transport the homology of the sphere $S^4$ to a homotopy $4$-sphere $M$ ($H_k(M;\mathbb Z)\cong H_k(S^4;\mathbb Z)$).
--
--   **Formalization Note** The homotopy equivalence is Mathlib's `ContinuousMap.HomotopyEquiv X Y`, the induced map is `SP4Homology.map k e.toFun`, and the conclusion is `IsIso` in `ModuleCat ℤ`. Mathlib proves that homotopic maps induce equal maps on singular homology (`TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor`); the statement here is its formal consequence for homotopy equivalences.
-- source:
--   Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002 (author's edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §2.1, Corollary 2.11, p. 111: "The maps f_* : Hₙ(X) → Hₙ(Y) induced by a homotopy equivalence f : X → Y are isomorphisms for all n" (a corollary of Theorem 2.10, homotopic maps induce the same homomorphism). Mathlib: Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean.

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy
import Definitions.Def_SP4Homology
import Definitions.Def_SP4HomologyMap

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission CategoryTheory Limits

theorem SP4Mission.homotopyEquiv_homology_isIso
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (k : ℕ) :
    IsIso (SP4Homology.map k e.toFun) := by sorry
