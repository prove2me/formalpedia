-- Prove2me | Theorems.Thm_SetOptLattice_Existence_Supplement_theorem_4_12
-- name    : SetOptLattice.Existence.Supplement.theorem_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:00:15.814931+00:00
-- url     : https://prove2.me/theorems/2b1df13e-74ef-4291-9ffc-6620bd09d3bd
-- title:
--   Theorem 4.12 — full well-posedness characterization, including the Sol-plus variant
-- statement:
--   Let $X$ be a separated topological linear space over $\mathbb R$, $(Z,\preceq)$ a preordered set, $\Psi$ a family of monotone maps $Z\to\overline{\mathbb R}$, and $f:X\to\mathcal P(Z,\Psi)$. Then
--   $$f\text{ is }(0,\Psi)\text{-well-posed}\quad\Longleftrightarrow\quad(1)\ \wedge\ (2)\ \wedge\ (3),$$
--   where the three conditions are:
--
--   1. $\operatorname{Min}(f,0,\Psi)$ is nonempty and belongs to $\operatorname{Sol}(f,0,\Psi)$.
--   2. Every arbitrary directed net of exact solution sets has a Hausdorff-convergent cofinal subnet whose limit is an exact solution set.
--   3. For every neighborhood $U$ of $0\in X$,
--   $$\exists\varepsilon>0\ \forall M\in\operatorname{Sol}(f,\varepsilon,\Psi)\ \exists N\in\operatorname{Sol}(f,0,\Psi):\quad M\subseteq N+U\ \wedge\ N\subseteq M+U.$$
--
--   The same equivalence holds after replacing only $\operatorname{Sol}(f,\varepsilon,\Psi)$ in condition (3) by $\operatorname{Sol}(f,\varepsilon+,\Psi)$. Conditions (1), (2), the exact limit solutions, and ordinary $(0,\Psi)$-well-posedness stay the same.
--
--   This companion theorem characterizes well-posedness by existence of a full exact solution, compactness in the subnet sense of the exact-solution family, and uniform approximation of all sufficiently accurate solutions. The tolerance may depend on $U$ but is uniform over $M$; one $N$ must satisfy both inclusions. No extra nonemptiness hypothesis on $\Psi$ is imposed: both sides are false for an empty family.
--
--   Differences from the source:
--   - encoding: arbitrary directed nets and genuine cofinal subnets → nontrivial image-tail filters and nontrivial finer filters on the set-valued carrier; reason: every such filter has a directed-net realization, and refinements lift to cofinal subnets of any original representing net; this avoids a bound on index universes
--   - reading: Hausdorff convergence without a standalone definition → both eventual neighborhood inclusions, with positive tolerances tending to zero; reason: the proof on p. 24 fixes this meaning; no metric or closed/bounded set restriction is introduced
--   - reading: Definition 4.8: "for all i > i_ε" (strict) the set M_i is an (ε,Ψ)-solution → eventually along the tail filter (all i ≥ i_ε); reason: the usual net tail; under the strict reading every net with a largest index would be Ψ-minimizing vacuously, so arbitrary constant nets would have to converge to solutions, which the paper (Example 4.10, proofs on pp. 27–28) does not intend
-- source:
--   Crespi, Hamel, Rocca, Schrage, arXiv:1812.03300v1, pp. 27–28, Theorem 4.12 and its Sol-plus variant on p. 28

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Supplement_WellPosedness

namespace SetOptLattice.Existence.Supplement

open Set Filter Topology
open scoped Pointwise

/-- Theorem 4.12, pp. 27–28. Both iff statements retain the entire three-condition
characterization. The announced variant changes only the positive-tolerance family
in condition (3), keeping exact solutions and ordinary well-posedness everywhere else. -/
theorem theorem_4_12 {X Z : Type*} [Preorder Z]
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℝ X] [T2Space X]
    (Ψ : Set (Z → EReal)) (hΨ : ∀ ψ ∈ Ψ, Monotone ψ)
    (f : X → Set Z) (hf : ∀ x, IsPsiClosed Ψ (f x)) :
    (IsWellPosed Ψ f ↔
      ((MinSet Ψ f 0).Nonempty ∧ MinSet Ψ f 0 ∈ Sol Ψ f 0) ∧
      HausdorffNetCompact (Sol Ψ f 0) ∧
      (∀ U ∈ 𝓝 (0 : X), ∃ ε : ℝ, 0 < ε ∧
        ∀ M ∈ Sol Ψ f ε, ∃ N ∈ Sol Ψ f 0, M ⊆ N + U ∧ N ⊆ M + U)) ∧
    (IsWellPosed Ψ f ↔
      ((MinSet Ψ f 0).Nonempty ∧ MinSet Ψ f 0 ∈ Sol Ψ f 0) ∧
      HausdorffNetCompact (Sol Ψ f 0) ∧
      (∀ U ∈ 𝓝 (0 : X), ∃ ε : ℝ, 0 < ε ∧
        ∀ M ∈ SolPlus Ψ f ε, ∃ N ∈ Sol Ψ f 0, M ⊆ N + U ∧ N ⊆ M + U)) := by sorry

end SetOptLattice.Existence.Supplement
