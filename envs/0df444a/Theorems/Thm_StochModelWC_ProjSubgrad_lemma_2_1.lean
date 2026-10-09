-- Prove2me | Theorems.Thm_StochModelWC_ProjSubgrad_lemma_2_1
-- name    : StochModelWC.ProjSubgrad.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:34:41.585604+00:00
-- url     : https://prove2.me/theorems/2b8bbb75-de9f-4a23-a7dd-de3b0dba60be
-- title:
--   Lemma 2.1 — subdifferential characterization of weak convexity
-- statement:
--   Let $\varphi : \mathbb R^d \to \mathbb R \cup \{+\infty\}$ be a closed (lower-semicontinuous) function with nonempty domain $D$, and let $\rho \in \mathbb R$. Then the following four statements are equivalent.
--
--   1. $\varphi$ is $\rho$-weakly convex: $x \mapsto \varphi(x) + \frac{\rho}{2}\|x\|^2$ is convex.
--   2. The approximate secant inequality holds: for all $x, y$ and $\lambda \in [0,1]$,
--   $$\varphi(\lambda x + (1-\lambda) y) \le \lambda\varphi(x) + (1-\lambda)\varphi(y) + \frac{\rho\lambda(1-\lambda)}{2}\|x - y\|^2. \tag{2.4}$$
--   3. The subgradient inequality holds: for all $x, y$ and $v \in \partial\varphi(x)$,
--   $$\varphi(y) \ge \varphi(x) + \langle v, y - x\rangle - \frac{\rho}{2}\|y - x\|^2. \tag{2.5}$$
--   4. The subdifferential is hypomonotone: for all $x, y$, $v \in \partial\varphi(x)$, $w \in \partial\varphi(y)$,
--   $$\langle v - w, x - y\rangle \ge -\rho\|x - y\|^2.$$
--
--   Here $\partial$ is the Fréchet subdifferential. Item 3 says that subgradients of a weakly convex function give concave quadratic under-estimators; it is the inequality (2.5) that the analysis of the projected stochastic subgradient method uses in step (3.8).
--
--   **Formalization Note.** $\varphi$ is given by its domain $D$ and its values on $D$. Item 2 is (2.4) read in extended arithmetic: for $x, y \in D$ the combination lies in $D$ and the inequality holds; pairs with $x$ or $y \notin D$ have right-hand side $+\infty$ and are omitted. Item 3 is stated for $y \in D$ (it is trivial otherwise). The paper's additional clause for $C^2$-smooth $\varphi$ ($\nabla^2\varphi \succeq -\rho I$) is not stated.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 10, Lemma 2.1 (items 1–4)

import Mathlib
import Definitions.Def_StochModelWC_ProjSubgrad_Basic

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace StochModelWC.ProjSubgrad

/-- Lemma 2.1 (p. 10), items 1–4, for a closed (lower-semicontinuous) proper `φ : ℝ^d → ℝ ∪ {∞}` encoded by its
domain `D` and its values on `D`. The C²-clause is not stated. -/
theorem lemma_2_1 {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d))) (φ : EuclideanSpace ℝ (Fin d) → ℝ) (ρ : ℝ)
    (hD : D.Nonempty) (hcl : IsClosedFn D φ) :
    List.TFAE
      [ IsWeaklyConvexOn D ρ φ,
        ∀ x ∈ D, ∀ y ∈ D, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          s • x + (1 - s) • y ∈ D ∧
          φ (s • x + (1 - s) • y) ≤ s * φ x + (1 - s) * φ y + ρ * s * (1 - s) / 2 * ‖x - y‖ ^ 2,
        ∀ x y : EuclideanSpace ℝ (Fin d), y ∈ D → ∀ v ∈ frechetSubdiff D φ x,
          φ x + ⟪v, y - x⟫_ℝ - ρ / 2 * ‖y - x‖ ^ 2 ≤ φ y,
        ∀ x y v w : EuclideanSpace ℝ (Fin d), v ∈ frechetSubdiff D φ x → w ∈ frechetSubdiff D φ y →
          -ρ * ‖x - y‖ ^ 2 ≤ ⟪v - w, x - y⟫_ℝ ] := by sorry

end StochModelWC.ProjSubgrad
