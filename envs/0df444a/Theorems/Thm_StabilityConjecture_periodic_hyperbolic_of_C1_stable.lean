-- Prove2me | Theorems.Thm_StabilityConjecture_periodic_hyperbolic_of_C1_stable
-- name    : StabilityConjecture.periodic_hyperbolic_of_C1_stable
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T08:58:11.288215+00:00
-- url     : https://prove2.me/theorems/ab9a65f2-a960-4495-996f-05aec7947f7e
-- title:
--   Periodic points of a $C^1$ structurally stable diffeomorphism are hyperbolic
-- statement:
--   Let $M$ be a closed manifold: a compact Hausdorff smooth manifold without boundary, modelled on $\mathbb R^n$. Let $f\in\mathrm{Diff}^1(M)$ be $C^1$ structurally stable: every diffeomorphism $g$ in some $C^1$ neighbourhood of $f$ is topologically conjugate to $f$. Then every periodic point of $f$ is hyperbolic:
--
--   $$\forall p\in\mathrm{Per}(f):\quad \{f^k(p):k\ge 0\}\ \text{is a hyperbolic set of } f .$$
--
--   This is one of the necessary conditions for structural stability, and the first step of the $C^1$ proof of the stability conjecture.
--
--   **Formalization Note** Hyperbolicity of a periodic point is stated as hyperbolicity of its finite orbit (definition `StabilityConjecture_Basic`), equivalent to the absence of eigenvalues of modulus one for $D(f^m)_p$, $m$ the period.
-- source:
--   J. Franks, Necessary conditions for stability of diffeomorphisms, Trans. Amer. Math. Soc. 158 (1971); also a consequence of R. Mañé, A proof of the C^1 stability conjecture, Publ. Math. IHÉS 66 (1988). Context: Open Problem Garden, "C^r Stability Conjecture" (Conjecture, author(s) J. Palis and S. Smale; posted by m n, December 20th, 2007), https://www.openproblemgarden.org/op/c_r_stability_conjecture

import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_StabilityConjecture_Basic

open scoped Manifold ContDiff Topology

namespace StabilityConjecture

open ClosingLemma

theorem periodic_hyperbolic_of_C1_stable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : Diff n M 1) (hf : IsStructurallyStable 1 f) :
    ∀ p ∈ Function.periodicPts f, IsHyperbolicPeriodicPt f p := by sorry

end StabilityConjecture
