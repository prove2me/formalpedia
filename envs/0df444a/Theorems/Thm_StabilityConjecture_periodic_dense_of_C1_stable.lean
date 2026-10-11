-- Prove2me | Theorems.Thm_StabilityConjecture_periodic_dense_of_C1_stable
-- name    : StabilityConjecture.periodic_dense_of_C1_stable
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T08:58:46.809122+00:00
-- url     : https://prove2.me/theorems/a36ca329-cbb5-4376-a506-d08e9bda98c5
-- title:
--   Periodic points are dense in $\Omega(f)$ for $C^1$ structurally stable $f$
-- statement:
--   Let $M$ be a closed manifold: a compact Hausdorff smooth manifold without boundary, modelled on $\mathbb R^n$. Let $f\in\mathrm{Diff}^1(M)$ be $C^1$ structurally stable. Then the periodic points of $f$ are dense in its nonwandering set:
--
--   $$\overline{\mathrm{Per}(f)}=\Omega(f).$$
--
--   This is the density half of Axiom A for $C^1$ structurally stable diffeomorphisms; for $C^r$, $r\ge2$, the corresponding statement is not known, since no $C^r$ closing lemma is available.
-- source:
--   Consequence of C. Pugh, An improved closing lemma and a general density theorem, Amer. J. Math. 89 (1967) (General Density Theorem), together with the invariance of Per(f) and Omega(f) under topological conjugacy; also contained in R. Mañé, A proof of the C^1 stability conjecture, Publ. Math. IHÉS 66 (1988). Context: Open Problem Garden, "C^r Stability Conjecture" (Conjecture, author(s) J. Palis and S. Smale; posted by m n, December 20th, 2007), https://www.openproblemgarden.org/op/c_r_stability_conjecture

import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_StabilityConjecture_Basic

open scoped Manifold ContDiff Topology

namespace StabilityConjecture

open ClosingLemma

theorem periodic_dense_of_C1_stable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : Diff n M 1) (hf : IsStructurallyStable 1 f) :
    closure (Function.periodicPts f) = PughClosingLemma.nonwanderingSet f := by sorry

end StabilityConjecture
