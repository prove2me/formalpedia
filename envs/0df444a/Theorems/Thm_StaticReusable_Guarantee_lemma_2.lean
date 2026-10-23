-- Prove2me | Theorems.Thm_StaticReusable_Guarantee_lemma_2
-- name    : StaticReusable.Guarantee.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:05.414484+00:00
-- url     : https://prove2.me/theorems/0cd19e58-0f68-420d-bdd8-fd3cb8bfd9c2
-- title:
--   Lemma 2, p. 15 — ∂R̃/∂z_1 ≥ 0 when y ≥ a_1z_1
-- statement:
--   Let $C \ge 4$ and $z_1, \dots, z_C \ge 0$ (with $z_{C+1} = 1$), and suppose $y = \sum_{k=2}^C a_k z_k \ge a_1 z_1$.
--   Then the function $t \mapsto \tilde R(t, z_2, \dots, z_C)$ is differentiable at $t = z_1$ and its derivative there is nonnegative:
--   $$\frac{\partial \tilde R}{\partial z_1}(z_1, \dots, z_C) \ge 0 .$$
--
--   With Lemma 3, this gives $\tilde R(z) \ge \tilde R(0, z_2, \dots, z_C) \ge 104/131$ in the case $y \ge a_1 z_1$.
--
--   **Formalization Note** The statement is the printed one, for all $z \in [0,\infty)^C$ with $y \ge a_1 z_1$. The paper's proof (p. ec5) additionally uses the inequalities (EC.2) $z_1 z_{k+1} \le z_2 z_k$, which hold for $z$ built from rates non-decreasing in $i$ (Lemma 1); they are not a hypothesis of the lemma as stated and are not assumed here. The derivative is stated as `HasDerivAt … d` with $d \ge 0$, not through `deriv`, which returns $0$ at points of non-differentiability.
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3, p. 15, Lemma 2

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace StaticReusable.Guarantee

theorem lemma_2 {C : ℕ} (hC : 4 ≤ C) (z : ℕ → ℝ) (hz : ∀ k ∈ Finset.Icc 1 C, 0 ≤ z k)
    (hy : a C 1 * z 1 ≤ ySum C z) :
    ∃ d : ℝ, HasDerivAt (fun t : ℝ => Rt C (Function.update z 1 t)) d (z 1) ∧ 0 ≤ d := by sorry
end StaticReusable.Guarantee
