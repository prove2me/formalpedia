-- Prove2me | Theorems.Thm_StabilityConjecture_palis_C1_omega_stability
-- name    : StabilityConjecture.palis_C1_omega_stability
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T09:00:16.420188+00:00
-- url     : https://prove2.me/theorems/b1ccb60d-222b-467d-9053-e2af9cd886df
-- title:
--   Palis' theorem: $C^1$ $\Omega$-stability implies Axiom A
-- statement:
--   Let $M$ be a closed manifold: a compact Hausdorff smooth manifold without boundary, modelled on $\mathbb R^n$. Let $f\in\mathrm{Diff}^1(M)$ be $C^1$ $\Omega$-stable: for every $g$ in some $C^1$ neighbourhood of $f$, the restrictions $f|_{\Omega(f)}$ and $g|_{\Omega(g)}$ are topologically conjugate. Then $f$ satisfies Axiom A: $\Omega(f)$ is a hyperbolic set of $f$ and
--
--   $$\overline{\mathrm{Per}(f)}=\Omega(f).$$
--
--   Since structural stability implies $\Omega$-stability, this strengthens the case $r=1$ of the stability conjecture.
--
--   **Formalization Note** Palis' theorem also gives the no-cycles condition for the spectral decomposition; that part is not included in this statement.
-- source:
--   J. Palis, On the C^1 Omega-stability conjecture, Publ. Math. IHÉS 66 (1988). Context: Open Problem Garden, "C^r Stability Conjecture" (Conjecture, author(s) J. Palis and S. Smale; posted by m n, December 20th, 2007), https://www.openproblemgarden.org/op/c_r_stability_conjecture

import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_StabilityConjecture_Basic

open scoped Manifold ContDiff Topology

namespace StabilityConjecture

open ClosingLemma

theorem palis_C1_omega_stability {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : Diff n M 1) (hf : IsOmegaStable 1 f) :
    SatisfiesAxiomA f := by sorry

end StabilityConjecture
