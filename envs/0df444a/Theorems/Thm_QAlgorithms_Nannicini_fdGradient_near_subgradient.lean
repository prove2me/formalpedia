-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_fdGradient_near_subgradient
-- name    : QAlgorithms.Nannicini.fdGradient_near_subgradient
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:46:26.925073+00:00
-- url     : https://prove2.me/theorems/62923fa8-ee4f-4df3-bd36-a4efc24b6683
-- title:
--   The central-difference gradient is within (η/2)Δ^(η)f(x) of every subgradient
-- statement:
--   Let $d \ge 0$, $\eta > 0$ and $x \in \mathbb{R}^d$, and write $B_1(x,\eta) = \{y \in \mathbb{R}^d : \|x - y\|_1 \le \eta\}$ for the closed $\ell_1$ ball. Let $f : B_1(x,\eta) \to \mathbb{R}$ be convex. For a function $f$ and step $\eta$, the finite-difference gradient and Laplace approximation at $x$ are
--
--   $$
--   \nabla^{(\eta)} f(x)_j = \frac{f(x+\eta e_j) - f(x-\eta e_j)}{2\eta}, \qquad \Delta^{(\eta)} f(x) = \sum_{j=1}^d \frac{f(x+\eta e_j) - 2 f(x) + f(x-\eta e_j)}{\eta^2},
--   $$
--
--   where $e_j$ is the $j$-th standard basis vector. A linear form $g$ on $\mathbb{R}^d$ is a subgradient of $f$ at $x$ if $f(y) \ge f(x) + \langle g, y - x\rangle$ for every $y \in B_1(x,\eta)$; the set of subgradients is $\partial f(x)$. Then every $g \in \partial f(x)$ satisfies
--
--   $$
--   \|g - \nabla^{(\eta)} f(x)\|_1 \le \frac{1}{2}\,\eta\,\Delta^{(\eta)} f(x),
--   $$
--
--   that is, $\sup_{g \in \partial f(x)} \|g - \nabla^{(\eta)} f(x)\|_1 \le \frac12 \eta \Delta^{(\eta)} f(x)$.
--
--   So when the Laplace approximation is small, the central-difference gradient is an accurate approximation of every subgradient; this is the first step in building a separation oracle from a membership oracle.
--
--   **Formalization Note** The supremum is stated as a bound for every subgradient, which avoids the default value of a real supremum. The function is a total function on $\mathbb{R}^d$ whose values off the ball are never used. A subgradient is a linear form $g$, and $\|g - \nabla^{(\eta)} f(x)\|_1$ is $\sum_j |g(e_j) - \nabla^{(\eta)} f(x)_j|$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 121, Lemma 5.28. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_GradientMethods
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open MeasureTheory

/-- Nannicini p.121, Lemma 5.28 (Lem. 10 in van Apeldoorn et al. 2020a). Let `η > 0`,
`x ∈ ℝ^d`, and `f : B_1(x, η) → ℝ` convex. Then
`sup_{g ∈ ∂f(x)} ‖g − ∇^(η) f(x)‖_1 ≤ (1/2) η Δ^(η) f(x)`.

The supremum is unfolded: every subgradient `g` of `f` at `x` (Def. 5.24, `g` a linear form,
the subgradient inequality over the domain `B_1(x, η)` of `f`) satisfies the bound; the ℓ1 norm
of `g − ∇^(η) f(x)` is `∑_j |g(e_j) − ∇^(η) f(x)_j|`. -/
theorem fdGradient_near_subgradient {d : ℕ} (η : ℝ) (hη : 0 < η) (x : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : ConvexOn ℝ (ballL1 x η) f)
    (g : Module.Dual ℝ (Fin d → ℝ)) (hg : IsEpsSubgradOn (ballL1 x η) f 0 x g) :
    ∑ j : Fin d, |g (Pi.single j 1) - fdGradient η f x j| ≤ 2⁻¹ * η * fdLaplacian η f x := by
  sorry




end QAlgorithms.Nannicini
