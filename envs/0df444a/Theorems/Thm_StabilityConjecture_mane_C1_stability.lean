-- Prove2me | Theorems.Thm_StabilityConjecture_mane_C1_stability
-- name    : StabilityConjecture.mane_C1_stability
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T08:59:33.215986+00:00
-- url     : https://prove2.me/theorems/66ad2d66-cec9-4456-8f98-5deb7b4cb5b9
-- title:
--   Mañé's theorem: $C^1$ structural stability implies Axiom A
-- statement:
--   Let $M$ be a closed manifold: a compact Hausdorff smooth manifold without boundary, modelled on $\mathbb R^n$. Let $f\in\mathrm{Diff}^1(M)$ be $C^1$ structurally stable. Then $f$ satisfies Axiom A: the nonwandering set $\Omega(f)$ is a hyperbolic set of $f$ and
--
--   $$\overline{\mathrm{Per}(f)}=\Omega(f).$$
--
--   This is the case $r=1$ of the $C^r$ stability conjecture, recorded as proved on the Open Problem Garden page.
-- source:
--   R. Mañé, A proof of the C^1 stability conjecture, Publ. Math. IHÉS 66 (1988). Recorded as the proved case r = 1 in Open Problem Garden, "C^r Stability Conjecture" (Conjecture, author(s) J. Palis and S. Smale; posted by m n, December 20th, 2007), https://www.openproblemgarden.org/op/c_r_stability_conjecture

import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_StabilityConjecture_Basic

open scoped Manifold ContDiff Topology

namespace StabilityConjecture

open ClosingLemma

theorem mane_C1_stability {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : Diff n M 1) (hf : IsStructurallyStable 1 f) :
    SatisfiesAxiomA f := by sorry

end StabilityConjecture
