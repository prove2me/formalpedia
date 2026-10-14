-- Prove2me | Theorems.Thm_StabilityConjecture_periodic_hyperbolic_of_hyperbolic_nonwandering
-- name    : StabilityConjecture.periodic_hyperbolic_of_hyperbolic_nonwandering
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-11T20:07:52.71769+00:00
-- url     : https://prove2.me/theorems/742ff4db-c6e9-4c32-9bc9-9dd9fd1de703
-- title:
--   If $\Omega(f)$ is hyperbolic, every periodic point of $f$ is hyperbolic
-- statement:
--   Let $M$ be a smooth manifold, $r\in\mathbb N$ and $f\in\mathrm{Diff}^r(M)$. If the nonwandering set $\Omega(f)$ is a hyperbolic set of $f$, then every periodic point $p$ of $f$ is hyperbolic, i.e. its orbit $\{f^k(p):k\ge0\}$ is a hyperbolic set of $f$.
--
--   The orbit of a periodic point is finite, hence compact, and $f$-invariant. Every periodic point is nonwandering, so the orbit lies in $\Omega(f)$, and the hyperbolic splitting and constants of $\Omega(f)$ restrict to it. In particular every diffeomorphism satisfying Axiom A has only hyperbolic periodic points.
--
--   **Formalization Note** $M$ is a smooth manifold modelled on $\mathbb R^n$ without boundary, $\mathrm{Diff}^r(M)$ is `ClosingLemma.Diff n M r` with the weak $C^r$ topology `ClosingLemma.crTopology r`, $\Omega(f)$ is `PughClosingLemma.nonwanderingSet f`, and hyperbolicity, Axiom A, structural stability and $\Omega$-stability are the mission definitions `IsHyperbolicSet`, `SatisfiesAxiomA`, `IsStructurallyStable`, `IsOmegaStable`.
-- source:
--   Standard fact of hyperbolic dynamics (a compact invariant subset of a hyperbolic set is hyperbolic; periodic points are nonwandering), e.g. M. Shub, Global Stability of Dynamical Systems (1987), and A. Katok and B. Hasselblatt, Introduction to the Modern Theory of Dynamical Systems (1995), §6.4. Mission "C^r Stability Conjecture (Palis–Smale)", https://www.openproblemgarden.org/op/c_r_stability_conjecture

import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_StabilityConjecture_Basic

open scoped Manifold ContDiff Topology

namespace StabilityConjecture

open ClosingLemma

/-- **Periodic orbits inside a hyperbolic nonwandering set are hyperbolic.** If `Ω(f)` is a
hyperbolic set of `f`, then every periodic point of `f` is a hyperbolic periodic point: its orbit
is a finite invariant subset of `Ω(f)`, and the hyperbolic splitting of `Ω(f)` restricts to it. -/
theorem periodic_hyperbolic_of_hyperbolic_nonwandering {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {r : ℕ} (f : Diff n M r) (hΩ : IsHyperbolicSet f (PughClosingLemma.nonwanderingSet f)) :
    ∀ p ∈ Function.periodicPts f, IsHyperbolicPeriodicPt f p := by sorry

end StabilityConjecture
