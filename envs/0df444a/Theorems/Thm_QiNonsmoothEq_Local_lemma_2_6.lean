-- Prove2me | Theorems.Thm_QiNonsmoothEq_Local_lemma_2_6
-- name    : QiNonsmoothEq.Local.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:50.258489+00:00
-- url     : https://prove2.me/theorems/cf3e250c-732e-4811-9a4f-5adc55194ac3
-- title:
--   Lemma 2.6, p. 233 — near a strongly BD-regular point every V ∈ ∂_B F(y) is nonsingular with ‖V⁻¹‖ ≤ c, and ‖h‖ ≤ c‖F′(y; h)‖ at semismooth y
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^n$ be locally Lipschitz and let $F$ be strongly BD-regular at $x$, i.e. every element of the B-subdifferential $\partial_B F(x)$ is nonsingular. Then there are a neighbourhood $N$ of $x$ and a constant $c$ such that:
--
--   1. for every $y\in N$ and every $V\in\partial_B F(y)$, $V$ is nonsingular and
--   $$\|V^{-1}\|\le c; \tag{2.13}$$
--   2. if moreover $F$ is semismooth at $y\in N$, then for every $h\in\mathbb R^n$
--   $$\|h\|\le c\,\|F'(y;h)\|. \tag{2.14}$$
--
--   The lemma propagates nonsingularity from the single point $x$ to a whole neighbourhood, with a uniform bound on the inverses; this is what makes the Newton step (3.2) well defined and controls its length near a strongly BD-regular zero.
--
--   **Formalization Note** "$V$ nonsingular with $\|V^{-1}\|\le c$" is the existence of a two-sided inverse $W$ of $V$ with $\|W\|\le c$. The same $N$ and $c$ serve both parts, as in the paper. Local Lipschitz continuity of $F$ is the paper's standing assumption (§1).
-- source:
--   Qi, Convergence analysis of some algorithms for solving nonsmooth equations, Math. Oper. Res. 18 (1993), p. 233, Lemma 2.6, (2.13)–(2.14)

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_NonsmoothNewton_Local_SemismoothAt
import Definitions.Def_QiNonsmoothEq_Local_Setting
open Filter Topology

namespace QiNonsmoothEq.Local

/-- Qi (1993), Lemma 2.6, p. 233. If `F` is strongly BD-regular at `x`, there are a
neighbourhood `N` of `x` and a constant `c` such that for every `y ∈ N` and `V ∈ ∂_B F(y)`,
`V` is nonsingular with `‖V⁻¹‖ ≤ c` (2.13); if `F` is also semismooth at `y ∈ N`, then
`‖h‖ ≤ c ‖F'(y; h)‖` for every `h` (2.14). -/
theorem lemma_2_6 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LocallyLipschitz F) (x : EuclideanSpace ℝ (Fin n))
    (hreg : StronglyBDRegularAt F x) :
    ∃ N ∈ 𝓝 x, ∃ c : ℝ,
      (∀ y ∈ N, ∀ V ∈ NonsmoothNewton.Shared.bJac F y,
        ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), IsInverse V W ∧ ‖W‖ ≤ c) ∧
      (∀ y ∈ N, NonsmoothNewton.Local.SemismoothAt F y →
        ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ c * ‖NonsmoothNewton.Local.dirDeriv F y h‖) := by sorry

end QiNonsmoothEq.Local
