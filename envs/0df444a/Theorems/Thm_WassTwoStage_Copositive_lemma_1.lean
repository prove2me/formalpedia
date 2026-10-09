-- Prove2me | Theorems.Thm_WassTwoStage_Copositive_lemma_1
-- name    : WassTwoStage.Copositive.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:55:26.287376+00:00
-- url     : https://prove2.me/theorems/3e1e5b3c-cb76-4f2f-badc-9bf0dec32388
-- title:
--   Lemma 1 — copositivity is tested on vectors with last entry 1
-- statement:
--   Let $M$ be a real symmetric $K\times K$ matrix. Then $M$ is copositive, i.e. $\xi^\top M\xi \ge 0$ for all $\xi\in\mathbb R^K_+$, if and only if
--   $$[z^\top\ 1]\, M\, [z^\top\ 1]^\top \ge 0 \qquad \forall z \in \mathbb R^{K-1}_+. \qquad (9)$$
--
--   This dehomogenization turns the semi-infinite constraints arising from the Lagrangian reformulation (13) into the copositive constraints of program (10).
--
--   **Formalization Note** The index set of $M$ is `Fin k ⊕ Unit`, i.e. $K = k + 1$ with the last coordinate (the `Unit` one) set to $1$; this avoids the natural-number subtraction $K - 1$. Copositivity is the platform definition `MurtyKabadi.Reduction.Copositive`.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, p. 8, Lemma 1, (9)

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems

open Matrix

namespace WassTwoStage.Copositive

/-- Lemma 1, Hanasusanto–Kuhn, arXiv:1609.07505v3, p. 8: a symmetric matrix `M ∈ 𝕊^K` is
copositive if and only if `[zᵀ 1] M [zᵀ 1]ᵀ ≥ 0` for all `z ∈ ℝ^{K−1}_+` (9). The index type
`Fin k ⊕ Unit` stands for `[K]` with `K = k + 1`; the `Unit` coordinate is the last one, set
to `1`. -/
theorem lemma_1 {k : ℕ} (Mt : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (hM : Mt.IsSymm) :
    MurtyKabadi.Reduction.Copositive Mt ↔
      ∀ z : Fin k → ℝ, 0 ≤ z →
        0 ≤ Sum.elim z (fun _ => (1 : ℝ)) ⬝ᵥ (Mt *ᵥ Sum.elim z (fun _ => (1 : ℝ))) := by sorry

end WassTwoStage.Copositive
