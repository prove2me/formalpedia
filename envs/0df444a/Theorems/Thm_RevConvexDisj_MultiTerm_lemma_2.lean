-- Prove2me | Theorems.Thm_RevConvexDisj_MultiTerm_lemma_2
-- name    : RevConvexDisj.MultiTerm.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:52.00423+00:00
-- url     : https://prove2.me/theorems/6e6b7767-5409-475f-88bc-595976b12ad0
-- title:
--   Lemma 2, p. 17 — nonnegative a, c with Σ a_i > 0 admit convex multipliers θ with a_iθ_0 = c_iθ_i
-- statement:
--   Let $s\ge 0$ and $a,c\in\mathbb{R}^s_+$ with $\sum_{i=1}^s a_i>0$. Then there is $\theta\in\mathbb{R}^{s+1}_+$, indexed by $0,1,\dots,s$, such that
--   $$\sum_{i=0}^s\theta_i = 1,\qquad a_i\theta_0 - c_i\theta_i = 0\quad (i=1,\dots,s)\qquad (32).$$
--
--   The paper derives it from Farkas' lemma and uses the multipliers $\theta$ to merge the representations of a point in all the terms $S^C_k$ into a representation in $T^C$ (proof of Theorem 5).
--
--   **Formalization Note.** The indices $0,\dots,s$ are `Fin (s+1)`; the paper's index $i\ge 1$ of $a_i,c_i$ is `i : Fin s`, and the corresponding $\theta_i$ is `θ i.succ`.
-- source:
--   Towle & Luedtke, Intersection disjunctions for reverse convex sets, arXiv:1901.02112v5, p. 17, Lemma 2, (32)

import Mathlib
import Definitions.Def_RevConvexDisj_MultiTerm_Model

namespace RevConvexDisj.MultiTerm

theorem lemma_2 (s : ℕ) (a c : Fin s → ℝ) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i)
    (hsum : 0 < ∑ i, a i) :
    ∃ θ : Fin (s + 1) → ℝ, (∀ i, 0 ≤ θ i) ∧ ∑ i, θ i = 1 ∧
      ∀ i : Fin s, a i * θ 0 - c i * θ i.succ = 0 := by sorry

end RevConvexDisj.MultiTerm
