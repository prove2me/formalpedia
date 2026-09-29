-- Prove2me | Theorems.Thm_Rudin_ch09_chain_rule
-- name    : Rudin.ch09_chain_rule
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:13:51.242143+00:00
-- url     : https://prove2.me/theorems/2cda470f-c572-4f67-90ed-90abfe34d121
-- title:
--   Theorem 9.15 — the chain rule
-- statement:
--   If $\mathbf{f}$ is differentiable at $\mathbf{x}$ with derivative $A$ and $\mathbf{g}$ is differentiable at $\mathbf{f}(\mathbf{x})$ with derivative $B$, then $\mathbf{g} \circ \mathbf{f}$ is differentiable at $\mathbf{x}$ with derivative $BA$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 9, p. 214, Theorem 9.15

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 9.15 (chain rule): if `f` is differentiable at `x` and `g` is differentiable
at `f x`, then `g ∘ f` is differentiable at `x` with derivative `g'(f x) ∘ f'(x)`. -/
theorem ch09_chain_rule (n m k : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k))
    (x : EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hf : HasFDerivAt f A x) (hg : HasFDerivAt g B (f x)) :
    HasFDerivAt (g ∘ f) (B.comp A) x := by sorry

end Rudin
