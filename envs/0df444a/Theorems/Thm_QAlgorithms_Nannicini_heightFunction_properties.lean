-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_heightFunction_properties
-- name    : QAlgorithms.Nannicini.heightFunction_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:47:51.116953+00:00
-- url     : https://prove2.me/theorems/8aebb71b-fa98-42e4-ba41-25f296063cb5
-- title:
--   Properties of the height function: convexity, Lipschitz continuity, and separation from an ϵ̄-subgradient (corrected)
-- statement:
--   This proposition collects the properties of the height function that underlie the construction of a separation oracle from a membership oracle. It is stated here in corrected form.
--
--   Let $d = m+1 \ge 1$ and let $K \subseteq \mathbb R^d$ be convex with $B_2(0,r) \subseteq K \subseteq B_2(0,R)$ for reals $0 < r < R$, where $B_2(c,\rho)$ is the closed Euclidean ball (Definition 5.20). Write points of $\mathbb R^d$ as $(y,t)$ with $y \in \mathbb R^{d-1}$ and $t \in \mathbb R$. Let $\epsilon > 0$ and $\tau > 0$, and let $x = -\tau e_d = (0,-\tau)$ satisfy $x \notin B_2(K,-\epsilon)$, that is, $B_2(x,\epsilon) \not\subseteq K$ (Definition 5.21). The height function is
--
--   $$
--   h : \mathbb R^{d-1} \to \mathbb R \cup \{\infty\}, \qquad h(y) = \inf\{t : (y,t) \in K\},
--   $$
--
--   with $h(y) = \infty$ when no such $t$ exists. Then:
--
--   1. $h$ is convex.
--   2. On $B_2(0, r/2) \subseteq \mathbb R^{d-1}$, $h$ is finite and Lipschitz continuous with constant $2R/r$.
--   3. Let $\bar\epsilon \in \mathbb R$ and let $g$ be an $\bar\epsilon$-subgradient of $h$ at $0$, i.e. $h(y) \ge h(0) + \langle g, y\rangle - \bar\epsilon$ for all $y$ (Definition 5.24). Put $a = (-g, 1) \in \mathbb R^d$ and $\bar b = \bar\epsilon + R\epsilon/r$. Then
--
--   $$
--   \langle a, z\rangle \ge \langle a, x\rangle - \bar b \qquad \text{for all } z \in K.
--   $$
--
--   Thus an approximate subgradient of $h$ at the origin, for instance one computed by finite differences or by the quantum gradient algorithm, yields a hyperplane through $x$ that has $K$ on one side up to the slack $\bar b$. This is the separation step of the membership-to-separation reduction.
--
--   **Formalization Note** The source leaves $\bar\epsilon$ and $\bar b$ "appropriately chosen" and writes $a = (g,1)$. Here $\bar\epsilon$ is arbitrary, $\bar b = \bar\epsilon + R\epsilon/r$ is explicit, and the sign of $g$ in $a$ is flipped, which the subgradient convention of Definition 5.24 requires. The height function takes values in the extended reals, so $\inf\emptyset = \infty$. Convexity is stated as convexity of the epigraph. Points $(y,t)$ are built by appending $t$ as the last coordinate.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 120, Proposition 5.25. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Nannicini_Ch05a_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini







/-- Corrected statement. Nannicini p.120–121, Proposition 5.25 (based on Lem. 19 and Lem. 21 of
van Apeldoorn et al. 2020a). Let `K ⊂ ℝ^d` (`d = m + 1`) be convex with
`B_2(0, r) ⊆ K ⊆ B_2(0, R)`, `0 < r < R`, let `ϵ > 0`, `τ > 0` (p.120) and
`x = −τ e_d ∉ B_2(K, −ϵ)`, i.e. `B_2(x, ϵ) ⊄ K` (Def. 5.21). Then the height function `h`
satisfies (i) it is convex (its epigraph is convex); (ii) it is finite and Lipschitz with constant
`2R/r` on `B_2(0, r/2)`; (iii) for every `ϵ̄` and every `g ∈ ∂_ϵ̄ h(0)` (Def. 5.24, with `h = ∞`
outside its domain), with `a = (−g, 1)`, every `z ∈ K` satisfies
`⟨a, z⟩ ≥ ⟨a, x⟩ − b̄` for `b̄ = ϵ̄ + Rϵ/r`.

Printed claim (iii): "if we take `g ∈ ∂_ϵ̄ h(0)` for an appropriately chosen value of `ϵ̄`, and let
`a = (g, 1)`, the half-space `⟨a, z⟩ ≥ ⟨a, x⟩ − b̄` separates `x` and `K` for an appropriately
chosen `b̄`". Changes: (1) `ϵ̄` is universally quantified, and `b̄` is the explicit value
`ϵ̄ + Rϵ/r`. The source omits both values ("We omit a discussion on the values of ϵ̄, b̄"), and
with `b̄` existential the claim is vacuous, because `K` is bounded. (2) `a = (−g, 1)` instead of
`(g, 1)`. With Def. 5.24's convention `h(y) ≥ h(0) + ⟨g, y⟩ − ϵ̄`, the printed sign fails for every
small `b̄`. Example (`d = 2`): `K = {|y| ≤ 1, |t| ≤ 1, t ≥ y/2 − 1/2}`, `r = 0.4`, `R = √2`,
`τ = 1/2`, `g = 1/2 ∈ ∂h(0)`, and `z = (−1, −1)` gives `⟨(g,1), z⟩ − ⟨(g,1), x⟩ = −1`. -/
theorem heightFunction_properties (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin (m + 1))))
    (hK : Convex ℝ K) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hin : Metric.closedBall 0 r ⊆ K) (hout : K ⊆ Metric.closedBall 0 R)
    (ε τ : ℝ) (hε : 0 < ε) (hτ : 0 < τ)
    (hx : ¬ Metric.closedBall (liftPoint 0 (-τ)) ε ⊆ K) :
    Convex ℝ {p : EuclideanSpace ℝ (Fin m) × ℝ | heightFunction K p.1 ≤ (p.2 : EReal)} ∧
    (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (r / 2),
      heightFunction K y ≠ ⊤ ∧ heightFunction K y ≠ ⊥) ∧
    (∀ y₁ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (r / 2),
      ∀ y₂ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (r / 2),
        |(heightFunction K y₁).toReal - (heightFunction K y₂).toReal| ≤ 2 * R / r * dist y₁ y₂) ∧
    ∀ (epsBar : ℝ) (g : EuclideanSpace ℝ (Fin m)),
      (∀ y, heightFunction K 0 + ((inner ℝ g y - epsBar : ℝ) : EReal) ≤ heightFunction K y) →
      ∀ z ∈ K, inner ℝ (liftPoint (-g) 1) (liftPoint 0 (-τ)) - (epsBar + R * ε / r) ≤
        inner ℝ (liftPoint (-g) 1) z := by
  sorry

end QAlgorithms.Nannicini
