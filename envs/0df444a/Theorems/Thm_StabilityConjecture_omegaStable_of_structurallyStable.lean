-- Prove2me | Theorems.Thm_StabilityConjecture_omegaStable_of_structurallyStable
-- name    : StabilityConjecture.omegaStable_of_structurallyStable
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-11T20:07:06.149807+00:00
-- url     : https://prove2.me/theorems/7098958b-ce04-46c3-acc0-2354d842d301
-- title:
--   Structural stability implies $\Omega$-stability
-- statement:
--   Let $M$ be a smooth manifold, $r\in\mathbb N$ and $f\in\mathrm{Diff}^r(M)$. If $f$ is $C^r$ structurally stable, then $f$ is $C^r$ $\Omega$-stable: there is a $C^r$ neighbourhood $\mathcal U$ of $f$ such that for every $g\in\mathcal U$ the restrictions $f|_{\Omega(f)}$ and $g|_{\Omega(g)}$ are topologically conjugate.
--
--   The reason is that a topological conjugacy $h\circ f=g\circ h$ of the whole manifold maps the nonwandering set $\Omega(f)$ homeomorphically onto $\Omega(g)$. Combined with Palis's $C^1$ $\Omega$-stability theorem, this gives Mañé's theorem that $C^1$ structurally stable diffeomorphisms satisfy Axiom A.
--
--   **Formalization Note** $M$ is a smooth manifold modelled on $\mathbb R^n$ without boundary, $\mathrm{Diff}^r(M)$ is `ClosingLemma.Diff n M r` with the weak $C^r$ topology `ClosingLemma.crTopology r`, $\Omega(f)$ is `PughClosingLemma.nonwanderingSet f`, and hyperbolicity, Axiom A, structural stability and $\Omega$-stability are the mission definitions `IsHyperbolicSet`, `SatisfiesAxiomA`, `IsStructurallyStable`, `IsOmegaStable`.
-- source:
--   Standard fact of hyperbolic dynamics (topological conjugacy preserves the nonwandering set), used to deduce Mañé's $C^1$ stability theorem from Palis's $C^1$ $\Omega$-stability theorem: J. Palis, "On the $C^1$ $\Omega$-stability conjecture", Publ. Math. IHÉS 66 (1988), 211–215; see also J. Palis and W. de Melo, Geometric Theory of Dynamical Systems (1982). Mission "C^r Stability Conjecture (Palis–Smale)", https://www.openproblemgarden.org/op/c_r_stability_conjecture

import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_StabilityConjecture_Basic

open scoped Manifold ContDiff Topology

namespace StabilityConjecture

open ClosingLemma

/-- **Structural stability implies `Ω`-stability.** A topological conjugacy `h ∘ f = g ∘ h` of the
whole manifold maps the nonwandering set `Ω(f)` homeomorphically onto `Ω(g)`, so a `C^r`
structurally stable diffeomorphism is `C^r` `Ω`-stable. -/
theorem omegaStable_of_structurallyStable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (r : ℕ) (f : Diff n M r) (hf : IsStructurallyStable r f) :
    IsOmegaStable r f := by sorry

end StabilityConjecture
