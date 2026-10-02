-- Prove2me | Theorems.Thm_SteinitzExchange_Extension_toReal_mem_hull_iff
-- name    : SteinitzExchange.Extension.toReal_mem_hull_iff
-- status  : Proved
-- author  : @choi
-- created : 2026-10-01T03:14:11.704125+00:00
-- url     : https://prove2.me/theorems/2477be5f-3d96-4f21-a520-32a1e295449a
-- title:
--   Equation (2.3) — an integral base set contains every lattice point of its convex hull
-- statement:
--   Let $V$ be a finite nonempty set and let $B\subseteq\mathbb Z^V$ be a finite integral base set: $B$ is nonempty and satisfies the one-sided base-exchange axiom (B1). Write $\overline B$ for its convex hull in $\mathbb R^V$. Then, for every integer vector $x\in\mathbb Z^V$,
--
--   $$x\in\overline B\quad\Longleftrightarrow\quad x\in B.$$
--
--   Thus the integer points of $\overline B$ are exactly $B$. This is Murota's equation (2.3), following the integral submodular-system characterization in Theorem 2.1. It transfers statements about integral base polytopes to their discrete base sets, including maximizer statements in the Extension Theorem.
--
--   **Formalization Note.** Integer vectors are embedded into real vectors by `toReal`, and `hull B` is their real convex hull.
-- source:
--   K. Murota, Convexity and Steinitz's Exchange Property, Advances in Mathematics 124 (1996), 272–311, §2.1, Eq. (2.3), following Theorem 2.1; DOI https://doi.org/10.1006/aima.1996.0084. Author manuscript (version January 16, 1997), §2.1, Eq. (2.3): https://scispace.com/pdf/convexity-and-steinitz-s-exchange-property-1h0w0a22vc.pdf

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet

namespace SteinitzExchange.Extension

theorem toReal_mem_hull_iff {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (x : V → ℤ) :
    toReal x ∈ hull B ↔ x ∈ B := by sorry

end SteinitzExchange.Extension
