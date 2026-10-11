-- Prove2me | Theorems.Thm_StabilityConjecture_cr_stability_conjecture
-- name    : StabilityConjecture.cr_stability_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T09:01:33.986808+00:00
-- url     : https://prove2.me/theorems/e05c7b58-d6f1-4093-9560-6f0505adba50
-- title:
--   $C^r$ Stability Conjecture: structurally stable diffeomorphisms satisfy Axiom A
-- statement:
--   Let $M$ be a closed manifold: a compact Hausdorff smooth manifold without boundary, modelled on $\mathbb R^n$. Let $r\ge 1$ be an integer and let $f\in\mathrm{Diff}^r(M)$ be $C^r$ structurally stable: there is a neighbourhood $\mathcal U$ of $f$ in $\mathrm{Diff}^r(M)$ (with the $C^r$ topology) such that every $g\in\mathcal U$ is topologically conjugate to $f$. Then $f$ is hyperbolic in the sense of Axiom A: the nonwandering set $\Omega(f)$ is a hyperbolic set of $f$ and
--
--   $$\overline{\mathrm{Per}(f)}=\Omega(f).$$
--
--   This is the Palis–Smale $C^r$ stability conjecture as stated on the Open Problem Garden ("any $C^r$ structurally stable diffeomorphism is hyperbolic"). The case $r=1$ was proved by Mañé; for $r\ge 2$ it is open.
--
--   **Formalization Note** $r$ ranges over natural numbers $\ge 1$ (the case $r=\infty$ is not covered). "Hyperbolic" is read as Axiom A (definition `StabilityConjecture_Basic`); the strong transversality condition of the full Palis–Smale characterization is not part of the statement.
-- source:
--   Open Problem Garden, "C^r Stability Conjecture" (Conjecture, author(s) J. Palis and S. Smale; posted by m n, December 20th, 2007), https://www.openproblemgarden.org/op/c_r_stability_conjecture (the boxed Conjecture: any C^r structurally stable diffeomorphism is hyperbolic; case r = 1 proved by R. Mañé, Publ. Math. IHÉS 66 (1988)).

import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_StabilityConjecture_Basic

open scoped Manifold ContDiff Topology

namespace StabilityConjecture

open ClosingLemma

theorem cr_stability_conjecture {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (r : ℕ) (hr : 1 ≤ r) (f : Diff n M r) (hf : IsStructurallyStable r f) :
    SatisfiesAxiomA f := by sorry

end StabilityConjecture
