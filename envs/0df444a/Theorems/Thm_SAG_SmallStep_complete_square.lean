-- Prove2me | Theorems.Thm_SAG_SmallStep_complete_square
-- name    : SAG.SmallStep.complete_square
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:08.25273+00:00
-- url     : https://prove2.me/theorems/66ff4215-239c-46e5-8a23-9df3a9a7fe00
-- title:
--   §A.5 Step 1, p. 21 — for symmetric negative definite $M$: $s^\top Ms+s^\top t\le-\frac14t^\top M^{-1}t$
-- statement:
--   Let $M$ be a real symmetric negative definite $m\times m$ matrix, and let $s,t\in\mathbb R^m$. Then
--   $$
--   s^\top Ms+s^\top t\;\le\;-\frac14\,t^\top M^{-1}t .
--   $$
--   The paper derives it from $(s+\frac12M^{-1}t)^\top M(s+\frac12M^{-1}t)\le0$.
--
--   In the proof of Proposition 1 this completion of the square removes the cross term between the gradient table and the iterate.
--
--   **Formalization Note** Negative definiteness is `(-M).PosDef`, which includes symmetry; $M^{-1}$ is Mathlib's matrix inverse, which is the true inverse because $M$ is invertible.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 21, §A.5 Step 1, "Note that for any symmetric negative definite matrix M …"

import Mathlib

open Matrix

namespace SAG.SmallStep

/-- §A.5 Step 1 (arXiv:1202.6258v4, p. 21): for a symmetric negative definite matrix `M` and
vectors `s`, `t`, `sᵀMs + sᵀt ≤ −¼ tᵀM⁻¹t`. -/
theorem complete_square {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (hM : (-M).PosDef)
    (s t : Fin m → ℝ) :
    s ⬝ᵥ (M *ᵥ s) + s ⬝ᵥ t ≤ -(1 / 4) * (t ⬝ᵥ (M⁻¹ *ᵥ t)) := by sorry

end SAG.SmallStep
