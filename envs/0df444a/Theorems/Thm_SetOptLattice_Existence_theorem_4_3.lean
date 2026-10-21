-- Prove2me | Theorems.Thm_SetOptLattice_Existence_theorem_4_3
-- name    : SetOptLattice.Existence.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:53.352754+00:00
-- url     : https://prove2.me/theorems/fec4dc39-4ded-4404-820b-fdde8f2f51ee
-- title:
--   Theorem 4.3, p. 23 — compact Min(f,ε+,Ψ) ⇒ Min(f,0+,Ψ) nonempty compact, Hausdorff limit; with lsc, Min(f,0,Ψ) a (0,Ψ)-solution
-- statement:
--   Let $X$ be a separated topological linear space over $\mathbb R$, $(Z,\preceq)$ a preordered set, $\Psi$ a non-empty family of monotone functions $\psi\colon Z\to\overline{\mathbb R}$ and $f\colon X\to\mathcal P(Z,\Psi)$. Let $\varepsilon_0>0$ be such that $\operatorname{Min}(f,\varepsilon+,\Psi)$ is compact for all $0<\varepsilon\le\varepsilon_0$. Then:
--
--   1. $\operatorname{Min}(f,0+,\Psi)$ is non-empty and compact, and $\operatorname{Min}(f,\varepsilon+,\Psi)$ Hausdorff converges to $\operatorname{Min}(f,0+,\Psi)$ as $\varepsilon\to0$: for every neighbourhood $U$ of $0\in X$ there is $\delta>0$ such that for all $0<\varepsilon<\delta$
--   $$\operatorname{Min}(f,\varepsilon+,\Psi)\subseteq\operatorname{Min}(f,0+,\Psi)+U\quad\text{and}\quad\operatorname{Min}(f,0+,\Psi)\subseteq\operatorname{Min}(f,\varepsilon+,\Psi)+U;$$
--   2. if, additionally, $\psi^\triangle\circ f$ is lower semicontinuous for all $\psi\in\Psi$, then $\operatorname{Min}(f,0,\Psi)$ is non-empty and a $(0,\Psi)$-solution of (P).
--
--   This is the paper's Weierstrass-type existence theorem with stability: approximate minimizer sets shrink, in the Hausdorff sense, onto the set of $(0+,\Psi)$-minimizers, and under lower semicontinuity the exact minimizers form a solution of the set optimization problem.
--
--   **Formalization Note** $\Psi\neq\emptyset$ is added: for $\Psi=\emptyset$ every $\operatorname{Min}$ set is empty, hence compact, and the non-emptiness claim fails. "Hausdorff converges" is not defined in the paper; the reading above (upper and lower, with arbitrary neighbourhoods $U$ of $0$) is the one used in the proof on p. 24. Lower semicontinuity of $\psi^\triangle\circ f$ is with respect to the order topology of $\overline{\mathbb R}$.
-- source:
--   Crespi, Hamel, Rocca, Schrage, arXiv:1812.03300v1, p. 23, Theorem 4.3; standing assumption of §4, p. 22; Hausdorff convergence as in the proof, p. 24

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

namespace SetOptLattice.Existence

open Set Filter Topology
open scoped Pointwise

/-- Theorem 4.3, p. 23: compactness of `Min (f, ε+, Ψ)` for `0 < ε ≤ ε₀` gives a nonempty
compact `Min (f, 0+, Ψ)`, the Hausdorff limit of `Min (f, ε+, Ψ)`; with lower semicontinuity of
every `ψ△ ∘ f`, `Min (f, 0, Ψ)` is a non-empty `(0, Ψ)`-solution of (P). -/
theorem theorem_4_3 {X Z : Type*} [Preorder Z]
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℝ X] [T2Space X]
    (Ψ : Set (Z → EReal)) (hΨ : ∀ ψ ∈ Ψ, Monotone ψ) (hΨne : Ψ.Nonempty)
    (f : X → Set Z) (hf : ∀ x, IsPsiClosed Ψ (f x))
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hcpt : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → IsCompact (MinPlusSet Ψ f ε)) :
    ((MinPlusSet Ψ f 0).Nonempty ∧ IsCompact (MinPlusSet Ψ f 0) ∧
        HausdorffConverges (MinPlusSet Ψ f) (MinPlusSet Ψ f 0)) ∧
      ((∀ ψ ∈ Ψ, LowerSemicontinuous (fun x => infExt ψ (f x))) →
        (MinSet Ψ f 0).Nonempty ∧ IsSolution Ψ f 0 (MinSet Ψ f 0)) := by sorry

end SetOptLattice.Existence
